#!/usr/bin/env node

/*
Run a Sage program on the public SageCell Jupyter service and print its text
output.  This is only a certificate generator: every generated identity is
subsequently checked by Lean's kernel.
*/

import { readFile } from "node:fs/promises";
import { randomUUID } from "node:crypto";

const sourcePath = process.argv[2];
if (!sourcePath) {
  throw new Error("usage: sagecell_client.mjs PROGRAM.sage");
}

const code = await readFile(sourcePath, "utf8");
const cellSessionId = `codex-${randomUUID()}`;
const kernelResponse = await fetch(
  `https://sagecell.sagemath.org/kernel?CellSessionID=${cellSessionId}` +
    "&timeout=0&accepted_tos=true",
  {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ name: "sage" }),
  },
);

if (!kernelResponse.ok) {
  throw new Error(`kernel start failed: ${kernelResponse.status} ${await kernelResponse.text()}`);
}

const { id, ws_url: wsUrl } = await kernelResponse.json();
const sessionId = randomUUID();
const socket = new WebSocket(
  `${wsUrl}kernel/${id}/channels?session_id=${sessionId}`,
);

const msgId = randomUUID();
let finished = false;
let exitCode = 0;

const cleanup = async () => {
  try {
    await fetch(`https://sagecell.sagemath.org/kernel/${id}`, { method: "DELETE" });
  } catch {
    // The remote kernel also has a short idle timeout.
  }
};

const timeout = setTimeout(async () => {
  console.error("SageCell execution timed out");
  exitCode = 1;
  socket.close();
  await cleanup();
  process.exit(exitCode);
}, 10 * 60 * 1000);

socket.onopen = () => {
  socket.send(JSON.stringify({
    header: {
      msg_id: msgId,
      username: "codex",
      session: sessionId,
      msg_type: "execute_request",
      version: "5.3",
      date: new Date().toISOString(),
    },
    parent_header: {},
    metadata: {},
    content: {
      code,
      silent: false,
      store_history: false,
      user_expressions: {},
      allow_stdin: false,
      stop_on_error: true,
    },
    channel: "shell",
    buffers: [],
  }));
};

socket.onmessage = async ({ data }) => {
  const message = JSON.parse(typeof data === "string" ? data : await data.text());
  const type = message.header?.msg_type;
  const content = message.content ?? {};

  if (type === "stream") {
    process.stdout.write(content.text ?? "");
  } else if (type === "execute_result" || type === "display_data") {
    if (content.data?.["text/plain"]) {
      process.stdout.write(`${content.data["text/plain"]}\n`);
    }
  } else if (type === "error") {
    process.stderr.write(`${(content.traceback ?? [content.evalue]).join("\n")}\n`);
    exitCode = 1;
  } else if (
    type === "status" &&
    content.execution_state === "idle" &&
    message.parent_header?.msg_id === msgId
  ) {
    finished = true;
    clearTimeout(timeout);
    socket.close();
    await cleanup();
  }
};

socket.onerror = (event) => {
  console.error("SageCell websocket error", event.message ?? event.type ?? event);
  exitCode = 1;
};

socket.onclose = async () => {
  clearTimeout(timeout);
  await cleanup();
  if (!finished && exitCode === 0) {
    console.error("SageCell websocket closed before execution completed");
    exitCode = 1;
  }
  process.exit(exitCode);
};
