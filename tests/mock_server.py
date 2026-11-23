"""Mock of the Anthropic Messages API for the ClaudeFFI tests.

Usage: python3 -I mock_server.py <expected-api-key> <certificate.pem> <private-key.pem>
The server binds 127.0.0.1 on a free port and prints the port on stdout.
It speaks HTTPS only, with TLS 1.2 or later.
The request's "model" field selects the behaviour:
  echo-utf8 / echo-ascii  return the first message's content as one text block
  status-NNN              return HTTP status NNN with a JSON error body
  blocks                  return the request's "blocks" field as the content array
  big-N                   return a text block of N copies of "x"
  refuse                  return an empty content with stop_reason "refusal"
  truncated               return the text "partial" with stop_reason "max_tokens"
  sim-*                   the simulated assistants of tests/Scenarios.lean, see below
Every 200 response carries "conn", a per-connection serial number.

The simulated assistants are deterministic functions of the request.
  sim-react     plans the operations of a "TASK op; op; ..." line, one "CALL" per reply
  sim-loop      always replies "CALL add 1 1"
  sim-garbage   replies outside the protocol
  sim-tools     requests the tool get_weather through tool_use blocks, one city per reply
  sim-script    plays the agent NAME of a "SCRIPT NAME" block. It replies with section K
                of the block, where K counts the turns of NAME in the thread that follows.
                A section may start with an "EXPECT text" line. The request then fails
                unless the thread contains the text.
"""
import http.server
import itertools
import json
import ssl
import sys

EXPECTED_KEY = sys.argv[1]
_conn_ids = itertools.count(1)


def text_of(content):
    """The text of a message content, which is a string or a list of blocks."""
    if isinstance(content, str):
        return content
    return "".join(b.get("text", "") for b in content if b.get("type") == "text")


def lines_with(prefix, text):
    """The remainders of the lines of `text` that start with `prefix`."""
    return [line[len(prefix):].strip() for line in text.split("\n") if line.startswith(prefix)]


def simulate(model, req):
    """The reply of a simulated assistant, as (content blocks, stop_reason).
    Raises ValueError when the request breaks the protocol of the assistant."""
    messages = req["messages"]
    roles = [m["role"] for m in messages]
    if roles != ["user", "assistant"] * (len(roles) // 2) + ["user"]:
        raise ValueError("roles do not alternate from user to user")
    last = text_of(messages[-1]["content"])

    def say(text):
        return [{"type": "text", "text": text}], "end_turn"

    if model == "sim-react":
        tasks = lines_with("TASK ", last)
        if len(tasks) != 1:
            raise ValueError("expected one TASK line")
        ops = [op.strip() for op in tasks[0].split(";")]
        results = lines_with("RESULT ", last)
        if len(results) < len(ops):
            previous = results[-1] if results else "0"
            return say("CALL " + ops[len(results)].replace("$", previous))
        return say("FINAL " + results[-1])
    if model == "sim-loop":
        return say("CALL add 1 1")
    if model == "sim-garbage":
        return say("I would rather talk about something else.")
    if model == "sim-tools":
        first = text_of(messages[0]["content"])
        if not first.startswith("weather in "):
            raise ValueError("expected a weather question")
        cities = [c.strip() for c in first[len("weather in "):].split(",")]
        results = []
        for i, m in enumerate(messages):
            if m["role"] != "user" or isinstance(m["content"], str):
                continue
            for block in m["content"]:
                if block.get("type") != "tool_result":
                    continue
                # The preceding assistant turn must carry the matching tool_use block.
                uses = [b for b in messages[i - 1]["content"]
                        if isinstance(b, dict) and b.get("type") == "tool_use"]
                if [u["id"] for u in uses] != [block["tool_use_id"]]:
                    raise ValueError("the history does not replay the tool_use block")
                if uses[0]["input"] != {"city": cities[len(results)]}:
                    raise ValueError("the history alters the tool input")
                results.append(block["content"])
        if len(results) < len(cities):
            city = cities[len(results)]
            return [{"type": "text", "text": "Checking " + city + "."},
                    {"type": "tool_use", "id": "toolu_%d" % len(results), "name": "get_weather",
                     "input": {"city": city}}], "tool_use"
        return say("; ".join(c + ": " + r for c, r in zip(cities, results)))
    if model == "sim-script":
        head, _, thread = last.partition("\nEND SCRIPT\n")
        first, _, body = head.partition("\n")
        if not first.startswith("SCRIPT "):
            raise ValueError("expected a SCRIPT block")
        name = first[len("SCRIPT "):]
        sections = body.split("\n=====\n")
        turns = sum(1 for line in thread.split("\n") if line == "## " + name)
        section = sections[min(turns, len(sections) - 1)]
        if section.startswith("EXPECT "):
            expected, _, section = section.partition("\n")
            if expected[len("EXPECT "):] not in thread:
                raise ValueError("the thread lacks the text: " + expected[len("EXPECT "):])
        return say(section)
    raise ValueError("unknown simulated assistant")


class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"  # keep-alive, so the client can reuse the connection

    def setup(self):
        super().setup()
        self.conn_id = next(_conn_ids)

    def log_message(self, *args):
        pass

    def send_json(self, status, obj, ascii_only=True):
        data = json.dumps(obj, ensure_ascii=ascii_only).encode("utf-8")
        self.send_response(status)
        self.send_header("content-type", "application/json")
        self.send_header("content-length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_POST(self):
        body = self.rfile.read(int(self.headers.get("content-length", "0")))
        if self.headers.get("anthropic-version") != "2023-06-01" or \
                self.headers.get("content-type") != "application/json":
            return self.send_json(400, {"type": "error", "error": {"type": "bad_headers"}})
        if self.headers.get("x-api-key") != EXPECTED_KEY:
            return self.send_json(401, {"type": "error", "error": {"type": "authentication_error"}})
        try:
            req = json.loads(body.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            return self.send_json(400, {"type": "error", "error": {"type": "invalid_json"}})
        model = req.get("model", "")
        if model in ("echo-utf8", "echo-ascii"):
            text = req["messages"][0]["content"]
            return self.send_json(200, {"content": [{"type": "text", "text": text}],
                                        "conn": self.conn_id}, model == "echo-ascii")
        if model.startswith("status-"):
            status = int(model[len("status-"):])
            return self.send_json(status, {"type": "error", "status": status})
        if model == "blocks":
            return self.send_json(200, {"content": req["blocks"], "conn": self.conn_id}, False)
        if model.startswith("big-"):
            n = int(model[len("big-"):])
            return self.send_json(200, {"content": [{"type": "text", "text": "x" * n}],
                                        "conn": self.conn_id})
        if model == "truncated":
            return self.send_json(200, {"content": [{"type": "text", "text": "partial"}],
                                        "stop_reason": "max_tokens", "conn": self.conn_id})
        if model == "refuse":
            return self.send_json(200, {"content": [], "stop_reason": "refusal",
                                        "conn": self.conn_id})
        if model.startswith("sim-"):
            try:
                content, stop = simulate(model, req)
            except (ValueError, KeyError, IndexError, TypeError) as e:
                return self.send_json(400, {"type": "error", "error": {
                    "type": "invalid_request_error", "message": str(e)}})
            return self.send_json(200, {"content": content, "stop_reason": stop,
                                        "conn": self.conn_id}, False)
        return self.send_json(400, {"type": "error", "error": {"type": "unknown_model"}})


context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
context.minimum_version = ssl.TLSVersion.TLSv1_2
context.load_cert_chain(sys.argv[2], sys.argv[3])
server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
server.socket = context.wrap_socket(server.socket, server_side=True)
print(server.server_address[1], flush=True)
server.serve_forever()
