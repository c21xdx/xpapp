const http = require('http');
const net = require('net');
const dgram = require('dgram');
const dns = require('dns');
const crypto = require('crypto');
const { EventEmitter } = require('events');

// ---------------------------------------------------------------- config

const PORT = parseInt(process.env.PORT || '3000', 10);
const HOST = process.env.HOST || '0.0.0.0';
const XPATH = (process.env.XPATH || '/nvle').replace(/\/+$/, '');
const MAX_CONN = parseInt(process.env.MAX_CONN || '1024', 10);
const ALLOW_PRIVATE = process.env.ALLOW_PRIVATE === '1';
const LOG = process.env.LOG || 'info';

const ID = (process.env.ID || process.env.UUID || '0cf85927-2c71-4e87-9df3-b1eb7d5a9e1b').toLowerCase();
if (!/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/.test(ID)) {
  console.error('bad ID:', ID);
  process.exit(1);
}
const ID_BYTES = Buffer.from(ID.replace(/-/g, ''), 'hex');

const log = LOG === 'silent' ? () => {} : console.log.bind(console);
const debug = LOG === 'debug' ? console.log.bind(console) : () => {};
const warn = LOG === 'silent' ? () => {} : console.error.bind(console);

const MAX_POST_BYTES = 2_000_000;
const MAX_BUFFERED_POSTS = 64;
const SESSION_TTL = 30_000;
const HANDSHAKE_TIMEOUT = 10_000;
const MAX_PENDING = 1 << 20;
const UDP_IDLE = 60_000;

// ---------------------------------------------------------------- LAN guard

const BLOCKED = new net.BlockList();
for (const [addr, bits] of [
  ['0.0.0.0', 8], ['10.0.0.0', 8], ['100.64.0.0', 10], ['127.0.0.0', 8],
  ['169.254.0.0', 16], ['172.16.0.0', 12], ['192.0.0.0', 24], ['192.168.0.0', 16],
  ['198.18.0.0', 15], ['224.0.0.0', 4], ['240.0.0.0', 4],
]) BLOCKED.addSubnet(addr, bits, 'ipv4');
for (const [addr, bits] of [['::', 128], ['::1', 128], ['fc00::', 7], ['fe80::', 10], ['ff00::', 8]])
  BLOCKED.addSubnet(addr, bits, 'ipv6');

const denied = (ip) => {
  if (ALLOW_PRIVATE) return false;
  const f = net.isIP(ip);
  return f !== 0 && BLOCKED.check(ip, f === 6 ? 'ipv6' : 'ipv4');
};

// wraps dns.lookup, rejects results pointing at LAN (also blocks rebinding)
function safeLookup(hostname, opts, cb) {
  dns.lookup(hostname, opts, (err, address, family) => {
    if (err) return cb(err);
    const list = Array.isArray(address) ? address : [{ address, family }];
    const ok = list.filter((e) => !denied(e.address));
    if (!ok.length) return cb(new Error('destination blocked: ' + hostname));
    cb(null, Array.isArray(address) ? ok : ok[0].address, ok[0].family);
  });
}

function resolveSafe(host, cb) {
  if (net.isIP(host)) return denied(host) ? cb(new Error('blocked')) : cb(null, host, net.isIP(host));
  safeLookup(host, {}, cb);
}

// ---------------------------------------------------------------- address codec

// reads an address starting at buf[off]; returns {host, off} or null
function readAddr(buf, off) {
  if (off >= buf.length) return null;
  const type = buf[off++];
  if (type === 0x01) {
    if (off + 4 > buf.length) return null;
    return { host: `${buf[off]}.${buf[off + 1]}.${buf[off + 2]}.${buf[off + 3]}`, off: off + 4 };
  }
  if (type === 0x02) {
    if (off >= buf.length) return null;
    const n = buf[off++];
    if (off + n > buf.length || n === 0) return null;
    return { host: buf.toString('utf8', off, off + n), off: off + n };
  }
  if (type === 0x03) {
    if (off + 16 > buf.length) return null;
    const parts = [];
    for (let i = 0; i < 8; i++, off += 2) parts.push(buf.readUInt16BE(off).toString(16));
    return { host: parts.join(':'), off };
  }
  return null;
}

// ---------------------------------------------------------------- core
// transport-agnostic; only relies on link's interface:
//   link.on('data'|'close'), link.send(buf)->bool, link.close()
//   link.pause()/resume(), link emits 'drain'

const NET = { 1: 'tcp', 2: 'udp', 3: 'mux' };
const OK = Buffer.from([0, 0]); // reply: version 0, no extra

function serve(link, peer) {
  const c = {
    id: link.id,
    link,
    peer,
    acc: Buffer.alloc(0),
    state: 'head',
    sessions: new Map(),
  };

  const timer = setTimeout(() => {
    if (c.state === 'head') {
      debug('handshake timeout', peer);
      link.close();
    }
  }, HANDSHAKE_TIMEOUT);

  link.on('data', (data) => {
    if (c.state === 'tcp') return c.feed(data);
    c.acc = c.acc.length ? Buffer.concat([c.acc, data]) : data;
    if (c.acc.length > MAX_PENDING) return link.close();
    try {
      if (c.state === 'head') parseHead(c);
      else if (c.state === 'udp') c.feed();
      else if (c.state === 'mux') muxFeed(c);
    } catch (e) {
      debug('parse error', c.id, e.message);
      link.close();
    }
  });

  link.once('close', () => {
    clearTimeout(timer);
    c.state = 'closed';
    for (const s of c.sessions.values()) s.close();
    c.sessions.clear();
    c.onClose?.();
  });
}

// header: ver(1) id(16) addonLen(1) addon cmd(1) port(2) addr
function parseHead(c) {
  const b = c.acc;
  if (b.length < 24) return;
  let off = 0;
  off++; // version
  const uid = b.subarray(off, (off += 16));
  const addonLen = b[off++];
  off += addonLen;
  if (off + 1 > b.length) return;
  const cmd = b[off++];

  if (!crypto.timingSafeEqual(uid, ID_BYTES)) {
    warn('auth failed', c.peer);
    return c.link.close();
  }

  const kind = NET[cmd];
  if (!kind) throw new Error('unknown cmd ' + cmd);

  if (kind === 'mux') {
    c.state = 'mux';
    c.acc = b.subarray(off);
    c.link.send(OK);
    return muxFeed(c);
  }

  if (off + 2 > b.length) return;
  const port = b.readUInt16BE(off);
  off += 2;
  const a = readAddr(b, off);
  if (!a) return;
  if (!port) throw new Error('bad port');

  c.state = kind;
  c.acc = b.subarray(a.off);
  c.link.send(OK);
  debug(kind, c.id, '->', a.host, port);
  if (kind === 'tcp') startTcp(c, a.host, port);
  else startUdp(c, a.host, port);
}

function startTcp(c, host, port) {
  if (net.isIP(host) && denied(host)) {
    warn('target blocked', host);
    return c.link.close();
  }
  const target = net.createConnection({ host, port, lookup: safeLookup });
  target.setNoDelay(true);
  target.setKeepAlive(true, 30_000);

  c.feed = (data) => {
    const chunk = data ? (c.acc.length ? Buffer.concat([c.acc, data]) : data) : c.acc;
    c.acc = Buffer.alloc(0);
    if (!chunk.length || target.destroyed) return;
    if (!target.write(chunk)) c.link.pause();
  };
  target.on('drain', () => c.link.resume());

  target.on('data', (d) => {
    if (!c.link.send(d)) target.pause();
  });
  c.link.on('drain', () => target.resume());

  target.on('error', (e) => debug('tcp error', c.id, e.code || e.message));
  target.on('close', () => c.link.close());
  c.onClose = () => target.destroy();

  if (c.acc.length) c.feed();
}

// payload format: [len:2][payload] repeated
function startUdp(c, host, port) {
  let sock = null;
  let ready = false;
  let queue = [];
  let dead = false;

  const flush = () => {
    if (!ready) return;
    for (const p of queue) sock.send(p);
    queue = [];
  };

  c.onClose = () => {
    dead = true;
    try {
      sock?.close();
    } catch {}
  };

  resolveSafe(host, (err, ip, family) => {
    if (err || dead || c.state === 'closed') return c.link.close();
    sock = dgram.createSocket(family === 6 ? 'udp6' : 'udp4');
    sock.on('message', (d) => {
      const n = Math.min(d.length, 65535);
      const out = Buffer.allocUnsafe(2 + n);
      out.writeUInt16BE(n, 0);
      d.copy(out, 2, 0, n);
      c.link.send(out);
    });
    sock.on('error', () => c.link.close());
    sock.once('close', () => c.link.close());
    sock.connect(port, ip, () => {
      ready = true;
      flush();
    });
  });

  c.feed = () => {
    const b = c.acc;
    let off = 0;
    while (off + 2 <= b.length) {
      const n = b.readUInt16BE(off);
      if (off + 2 + n > b.length) break;
      queue.push(b.subarray(off + 2, off + 2 + n));
      off += 2 + n;
    }
    c.acc = b.subarray(off);
    flush();
  };
  if (c.acc.length) c.feed();
}

// frame: [metaLen:2][meta][dataLen:2][data]?   meta: id(2) cmd(1) opt(1) ...
function muxFeed(c) {
  for (;;) {
    const b = c.acc;
    if (b.length < 2) return;
    const metaLen = b.readUInt16BE(0);
    if (metaLen < 4) throw new Error('bad meta');
    if (b.length < 2 + metaLen) return;
    const meta = b.subarray(2, 2 + metaLen);
    let off = 2 + metaLen;
    let data = null;
    if (meta[3] & 1) {
      if (b.length < off + 2) return;
      const n = b.readUInt16BE(off);
      if (b.length < off + 2 + n) return;
      data = b.subarray(off + 2, off + 2 + n);
      off += 2 + n;
    }
    c.acc = b.subarray(off);
    muxFrame(c, meta, data);
    if (c.state === 'closed') return;
  }
}

function muxFrame(c, meta, data) {
  const uid = meta.readUInt16BE(0);
  const cmd = meta[2];
  if (cmd === 1) return muxNew(c, uid, meta, data);
  if (cmd === 4) return; // keepalive
  const s = c.sessions.get(uid);
  if (!s) return muxEnd(c, uid);
  if (cmd === 2) s.send(data);
  else if (cmd === 3) {
    c.sessions.delete(uid);
    s.close();
  } else throw new Error('bad cmd ' + cmd);
}

// new frame meta tail: network(1) port(2) addr
function muxNew(c, uid, meta, data) {
  const kind = NET[meta[4]];
  const port = meta.readUInt16BE(5);
  const a = kind && readAddr(meta, 7);
  if (!a || !port || kind === 'mux') return muxEnd(c, uid);

  debug('sub', kind, c.id + '/' + uid, '->', a.host, port);
  const s = kind === 'tcp' ? muxTcp(c, uid, a.host, port) : muxUdp(c, uid, a.host, port);
  c.sessions.set(uid, s);
  if (data && data.length) s.send(data);
}

function muxTcp(c, uid, host, port) {
  if (net.isIP(host) && denied(host)) {
    muxEnd(c, uid);
    return { send() {}, close() {} };
  }
  const t = net.createConnection({ host, port, lookup: safeLookup });
  t.setNoDelay(true);
  t.setKeepAlive(true, 30_000);
  t.on('data', (d) => muxKeep(c, uid, d));
  t.on('error', (e) => debug('sub tcp error', c.id + '/' + uid, e.code || e.message));
  t.once('close', () => {
    if (c.sessions.delete(uid)) muxEnd(c, uid);
  });
  return {
    send: (d) => d && d.length && !t.destroyed && t.write(d),
    close: () => t.destroy(),
  };
}

function muxUdp(c, uid, host, port) {
  const s = dgram.createSocket('udp4');
  let last = Date.now();
  s.on('message', (d) => {
    last = Date.now();
    muxKeep(c, uid, d);
  });
  s.on('error', () => close());
  const timer = setInterval(() => Date.now() - last > UDP_IDLE && close(), 10_000);
  let dead = false;
  function close() {
    if (dead) return;
    dead = true;
    clearInterval(timer);
    try {
      s.close();
    } catch {}
    if (c.sessions.delete(uid)) muxEnd(c, uid);
  }
  return {
    send: (d) => {
      if (dead || !d || !d.length) return;
      last = Date.now();
      resolveSafe(host, (err, ip) => !err && !dead && s.send(d, port, ip, () => {}));
    },
    close,
  };
}

function muxWrite(link, meta, data) {
  const n = data ? data.length : 0;
  const out = Buffer.allocUnsafe(2 + meta.length + (data ? 2 + n : 0));
  out.writeUInt16BE(meta.length, 0);
  meta.copy(out, 2);
  if (data) {
    out.writeUInt16BE(n, 2 + meta.length);
    data.copy(out, 4 + meta.length);
  }
  return link.send(out);
}

function muxKeep(c, uid, data) {
  if (!c.link.open) return;
  const meta = Buffer.from([uid >> 8, uid & 255, 2, 1]);
  for (let off = 0; off < data.length; ) {
    const n = Math.min(data.length - off, 65535);
    muxWrite(c.link, meta, data.subarray(off, off + n));
    off += n;
  }
}

function muxEnd(c, uid) {
  if (c.link.open) muxWrite(c.link, Buffer.from([uid >> 8, uid & 255, 3, 0]), null);
}

// ---------------------------------------------------------------- transport

let idSeq = 0;
let conns = 0;
const sessions = new Map(); // sessionId -> Link

/*
 * One session. Uplink comes from several out-of-order POSTs (reordered by
 * seq) or a single streaming request body; downlink is one long-lived GET
 * response. Exposed to the core as a plain duplex stream.
 */
class Link extends EventEmitter {
  constructor(id) {
    super();
    this.id = id;
    this.open = true;
    this.down = null; // downlink ServerResponse
    this.pendingDown = []; // buffer before GET arrives
    this.nextSeq = 0;
    this.heap = new Map(); // seq -> Buffer, reorder
    this.upReq = null; // streaming uplink request
    this.paused = false;
  }

  // fragmented mode: insert by seq, emit in order
  pushSeq(seq, payload) {
    if (!this.open) return true;
    if (seq < this.nextSeq) return true; // dup, drop
    this.heap.set(seq, payload);
    if (this.heap.size > MAX_BUFFERED_POSTS) {
      debug('reorder buffer overflow', this.id);
      this.close();
      return false;
    }
    for (;;) {
      const p = this.heap.get(this.nextSeq);
      if (p === undefined) break;
      this.heap.delete(this.nextSeq);
      this.nextSeq++;
      if (p.length) this.emit('data', p);
    }
    return true;
  }

  // streaming modes: request body is the uplink
  attachUplink(req) {
    this.upReq = req;
    clearTimeout(this.reaper);
    this.reaper = null;
    req.on('data', (d) => this.emit('data', d));
    req.on('error', () => this.close());
    req.on('end', () => {
      if (this.down === null) this.close();
    });
  }

  // bind downlink response, flush buffer
  attachDownlink(res) {
    this.down = res;
    res.on('drain', () => this.emit('drain'));
    res.on('close', () => this.close());
    res.on('error', () => this.close());
    let ok = true;
    for (const b of this.pendingDown) ok = res.write(b);
    this.pendingDown = [];
    if (ok) this.emit('drain');
  }

  // returns false when upstream should pause
  send(buf) {
    if (!this.open) return false;
    if (!this.down) {
      this.pendingDown.push(buf);
      let total = 0;
      for (const b of this.pendingDown) total += b.length;
      if (total > MAX_PENDING) {
        this.close();
        return false;
      }
      return false;
    }
    return this.down.write(buf);
  }

  pause() {
    if (this.paused) return;
    this.paused = true;
    this.upReq?.pause();
  }

  resume() {
    if (!this.paused) return;
    this.paused = false;
    this.upReq?.resume();
  }

  close() {
    if (!this.open) return;
    this.open = false;
    conns--;
    sessions.delete(this.sid);
    clearTimeout(this.reaper);
    try {
      this.down?.end();
    } catch {}
    try {
      this.upReq?.destroy();
    } catch {}
    this.heap.clear();
    this.pendingDown = [];
    this.emit('close');
  }
}

// random padding so response length is not fixed
const pad = () => 'X'.repeat(100 + Math.floor(Math.random() * 900));

function baseHeaders(res) {
  res.setHeader('X-Padding', pad());
  res.setHeader('Cache-Control', 'no-store');
}

const server = http.createServer((req, res) => {
  const qs = req.url.indexOf('?');
  const path = qs === -1 ? req.url : req.url.slice(0, qs);

  // anything off-path returns 404, no service fingerprint
  if (path !== XPATH && !path.startsWith(XPATH + '/')) {
    res.writeHead(404, { 'Content-Type': 'text/plain' }).end('Not Found');
    return;
  }

  if (req.method === 'OPTIONS') {
    baseHeaders(res);
    res.writeHead(200, {
      'Access-Control-Allow-Origin': '*',
      'Access-Control-Allow-Methods': '*',
      'Access-Control-Allow-Headers': '*',
    });
    res.end();
    return;
  }

  // default placement: sessionId and seq both in path -> /{XPATH}/{sid}/{seq}
  const rest = path.slice(XPATH.length).replace(/^\//, '');
  const parts = rest.length ? rest.split('/') : [];
  const sid = parts[0] || '';
  const seqStr = parts[1] || '';

  if (sid && !/^[\w.-]{1,64}$/.test(sid)) {
    res.writeHead(400).end();
    return;
  }

  const peer = `${req.socket.remoteAddress}:${req.socket.remotePort}`;
  const isGet = req.method === 'GET';
  // GET with seq counts as uplink; every other method is uplink
  const isUplink = isGet ? seqStr !== '' : true;

  // ---- uplink ----
  if (isUplink && sid) {
    const link = sessions.get(sid);

    if (seqStr === '') {
      // streaming uplink: request body is a continuous upload.
      // the client opens the downlink GET before this POST, so the session
      // usually already exists; only a duplicate uplink is a conflict.
      if (link && link.upReq) {
        res.writeHead(409).end();
        return;
      }
      const l = link || newLink(sid, peer);
      if (!l) {
        res.writeHead(503).end();
        return;
      }
      baseHeaders(res);
      res.setHeader('X-Accel-Buffering', 'no');
      res.writeHead(200);
      if (res.flushHeaders) res.flushHeaders();
      l.attachUplink(req);
      l.once('close', () => {
        try {
          res.end();
        } catch {}
      });
      return;
    }

    // fragmented mode: one POST = one numbered fragment
    const seq = Number(seqStr);
    if (!Number.isSafeInteger(seq) || seq < 0) {
      res.writeHead(400).end();
      return;
    }
    // a POST may arrive before the GET; create on demand
    const l = link || newLink(sid, peer);
    if (!l) {
      res.writeHead(503).end();
      return;
    }

    const chunks = [];
    let size = 0;
    let bad = false;
    req.on('data', (d) => {
      if (bad) return;
      size += d.length;
      if (size > MAX_POST_BYTES) {
        bad = true;
        res.writeHead(413).end();
        req.destroy();
        return;
      }
      chunks.push(d);
    });
    req.on('end', () => {
      if (bad) return;
      l.pushSeq(seq, chunks.length === 1 ? chunks[0] : Buffer.concat(chunks));
      baseHeaders(res);
      res.writeHead(200);
      res.end();
    });
    req.on('error', () => {});
    return;
  }

  // ---- downlink, or single-connection mode ----
  if (isGet || !sid) {
    let l;
    if (sid) {
      l = sessions.get(sid) || newLink(sid, peer);
      if (!l) {
        res.writeHead(503).end();
        return;
      }
      clearTimeout(l.reaper); // GET arrived, stop reaper
      l.reaper = null;
      if (l.down) {
        res.writeHead(409).end();
        return;
      }
    } else {
      // single-connection mode: no session id, body uplink + response downlink
      l = newLink(null, peer);
      if (!l) {
        res.writeHead(503).end();
        return;
      }
      l.attachUplink(req);
    }

    baseHeaders(res);
    // keep front proxies / CDNs from buffering the downlink
    res.setHeader('X-Accel-Buffering', 'no');
    res.setHeader('Content-Type', 'text/event-stream');
    res.writeHead(200);
    if (res.flushHeaders) res.flushHeaders();
    req.socket.setNoDelay(true);
    l.attachDownlink(res);
    return;
  }

  res.writeHead(405).end();
});

function newLink(sid, peer) {
  if (conns >= MAX_CONN) return null;
  conns++;
  const l = new Link(++idSeq);
  l.sid = sid;
  if (sid) {
    sessions.set(sid, l);
    // reap if the GET never shows up, to avoid half-open pile-up
    l.reaper = setTimeout(() => {
      debug('session reaped', sid);
      l.close();
    }, SESSION_TTL);
  }
  serve(l, peer);
  return l;
}

server.on('clientError', (_e, sock) => sock.destroy());
server.keepAliveTimeout = 120_000;
server.headersTimeout = 125_000;
server.requestTimeout = 0; // downlink GET and streaming uplink are long-lived

server.listen(PORT, HOST, () => {
  log(`listening on ${HOST}:${PORT} path=${XPATH}`);
});

let lastConns = -1;
const stat = setInterval(() => {
  if (conns !== lastConns) debug('sessions:', conns);
  lastConns = conns;
}, 5000);
stat.unref();

for (const sig of ['SIGINT', 'SIGTERM'])
  process.on(sig, () => {
    server.close();
    process.exit(0);
  });
process.on('uncaughtException', (e) => warn('uncaught', e.message));
