#!/usr/bin/env node

/* Run the p = 19 Sage generator in restartable batches and save exact JSON. */

import { readFile, unlink, writeFile } from "node:fs/promises";
import { randomUUID } from "node:crypto";

const sourcePath = new URL("./generate_19_certificates.sage", import.meta.url);
const outputPath = new URL("./certificates_19.json", import.meta.url);
const partialPath = new URL("./certificates_19.partial.json", import.meta.url);
const source = await readFile(sourcePath, "utf8");
const bound = 105933;
const batchSize = 10000;

async function cleanupKernel(id) {
  try {
    await fetch(`https://sagecell.sagemath.org/kernel/${id}`, { method: "DELETE" });
  } catch {
    // SageCell also reaps idle kernels.
  }
}

async function runBatch(lower, upper) {
  const code = `LOWER_BOUND=${lower}\nUPPER_BOUND=${upper}\n${source}`;
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
  const socket = new WebSocket(`${wsUrl}kernel/${id}/channels?session_id=${sessionId}`);
  const msgId = randomUUID();
  let output = "";
  let error = "";

  try {
    return await new Promise((resolve, reject) => {
      let finished = false;
      const timeout = setTimeout(() => {
        if (!finished) reject(new Error(`SageCell batch ${lower}-${upper} timed out`));
      }, 5 * 60 * 1000);

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
          if (content.name === "stderr") error += content.text ?? "";
          else output += content.text ?? "";
        } else if (type === "execute_result" || type === "display_data") {
          if (content.data?.["text/plain"]) output += `${content.data["text/plain"]}\n`;
        } else if (type === "error") {
          error += `${(content.traceback ?? [content.evalue]).join("\n")}\n`;
        } else if (
          type === "status" &&
          content.execution_state === "idle" &&
          message.parent_header?.msg_id === msgId
        ) {
          finished = true;
          clearTimeout(timeout);
          if (error) reject(new Error(error));
          else {
            try {
              resolve(JSON.parse(output.trim()));
            } catch (parseError) {
              reject(new Error(`invalid JSON for batch ${lower}-${upper}: ${parseError.message}`));
            }
          }
          socket.close();
        }
      };

      socket.onerror = () => {
        if (!finished) reject(new Error(`SageCell websocket error in batch ${lower}-${upper}`));
      };
      socket.onclose = () => {
        clearTimeout(timeout);
        if (!finished) reject(new Error(`SageCell closed during batch ${lower}-${upper}`));
      };
    });
  } finally {
    socket.close();
    await cleanupKernel(id);
  }
}

let state = { completedUpper: 2, certificates: [] };
try {
  state = JSON.parse(await readFile(partialPath, "utf8"));
  console.log(`resuming at ${state.completedUpper} with ${state.certificates.length} certificates`);
} catch (error) {
  if (error.code !== "ENOENT") throw error;
}

for (let lower = state.completedUpper; lower <= bound; lower += batchSize) {
  const upper = Math.min(lower + batchSize, bound + 1);
  console.log(`generating primes in [${lower}, ${upper})`);
  const batch = await runBatch(lower, upper);
  if (batch.bound !== bound || batch.class_number !== 1) {
    throw new Error(`unexpected Sage metadata in batch ${lower}-${upper}`);
  }
  state.certificates.push(...batch.certificates);
  state.completedUpper = upper;
  await writeFile(partialPath, `${JSON.stringify(state)}\n`);
  console.log(`saved batch of ${batch.certificates.length}; total ${state.certificates.length}`);
}

state.certificates.sort((a, b) => a.p - b.p);
if (state.certificates.length !== 558) {
  throw new Error(`expected 558 certificates, got ${state.certificates.length}`);
}
await writeFile(outputPath, `${JSON.stringify({
  bound,
  class_number: 1,
  certificates: state.certificates,
})}\n`);
await unlink(partialPath);
console.log(`saved 558 certificates to ${outputPath.pathname}`);
