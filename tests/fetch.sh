#!/usr/bin/env bash
# Stands up a plaintext server that frames one body by Content-Length and the
# other in chunks, and runs ez's own client against it on both lanes.
#   ./tests/fetch.sh
set -u
cd "$(dirname "$0")/.."
export BEND_LIB=$PWD/.ez/lib
mkdir -p .gate
trap 'st=$?; kill %1 2>/dev/null; rm -f .gate/netport; exit $st' EXIT
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then pass=$((pass + 1)); else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}

# a port of our own, so a stray server elsewhere cannot answer
port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
python3 - "$port" <<'PY' &
import socket, sys, threading

PLAIN = b"a manifest line\n"
CHUNKS = [b"one ", b"two ", b"three ", b"four\n"]

def reply(path):
    if path == "/plain":
        return (b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n"
                b"Content-Length: %d\r\nConnection: close\r\n\r\n" % len(PLAIN)) + PLAIN
    if path == "/chunked":
        body = b"".join(b"%x\r\n%s\r\n" % (len(c), c) for c in CHUNKS) + b"0\r\n\r\n"
        return (b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n"
                b"Connection: close\r\n\r\n") + body
    return b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"

def serve(c):
    head = b""
    while b"\r\n\r\n" not in head:
        part = c.recv(4096)
        if not part:
            c.close()
            return
        head += part
    path = head.split(b" ")[1].decode()
    out = reply(path)
    # the chunked body goes out in pieces, so the client meets a chunk that
    # straddles two reads
    for at in range(0, len(out), 7):
        c.sendall(out[at:at + 7])
    c.shutdown(socket.SHUT_WR)
    c.close()

s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("127.0.0.1", int(sys.argv[1])))
s.listen(16)
while True:
    c, _ = s.accept()
    threading.Thread(target=serve, args=(c,), daemon=True).start()
PY
for _ in $(seq 50); do
  python3 -c 'import socket,sys; socket.create_connection(("127.0.0.1",int(sys.argv[1])),1).close()' "$port" 2>/dev/null && break
  sleep 0.1
done
echo "$port" > .gate/netport

want=$(sed -n 's/^#|//p' tests/fetch.bend)
quiet() { awk -f bin/quiet.awk; }
check "tests/fetch.bend (js)" "$want" "$(bend tests/fetch.bend 2>&1 | quiet)"
if built=$(bend tests/fetch.bend -o .gate/fetch 2>&1 | quiet); then
  check "tests/fetch.bend (cpu)" "$want" "$(.gate/fetch --gpu off 2>&1 | quiet)"
else
  check "tests/fetch.bend (build)" "" "$built"
fi

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]
