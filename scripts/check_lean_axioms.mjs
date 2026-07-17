#!/usr/bin/env node

/* Enforce the exact axiom boundary promised by the Lean audit files. */

import { readFileSync } from "node:fs";

const output = readFileSync(0, "utf8");
const declarationsWithAxioms = [...output.matchAll(/depends on axioms:/g)].length;
const reports = [...output.matchAll(/depends on axioms:\s*\[([^\]]*)\]/gs)];

if (reports.length !== declarationsWithAxioms) {
  throw new Error("could not parse every '#print axioms' report");
}

const allowed = new Set(["propext", "Classical.choice", "Quot.sound"]);
for (const [, body] of reports) {
  const axioms = body.split(",").map((axiom) => axiom.trim()).filter(Boolean);
  const unexpected = axioms.filter((axiom) => !allowed.has(axiom));
  if (unexpected.length > 0) {
    throw new Error(`unexpected Lean axiom(s): ${unexpected.join(", ")}`);
  }
}
