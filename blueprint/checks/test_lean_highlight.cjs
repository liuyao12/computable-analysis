"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const {tokenize} = require("../three-proofs/lean-highlight.js");
const samples = [
  "theorem demo (x : ℚ) : x = x := by rfl",
  "/- outside /- inside -/ outside -/\ndef f' : Nat := 0xF",
  'def «odd name» : String := "<script>alert(1)</script>"',
  "∀ (a : Rat), a ≤ 1/2 → ℝ", "def c := 'λ'", "def x := \"escaped\"",
  "-- a line comment\nlet x := 4",
];
for (const text of samples) assert.equal(tokenize(text).map(t=>t.text).join(""),text);
assert.equal(tokenize(samples[1])[0].kind,"comment");
assert(tokenize(samples[0]).some(t=>t.kind==="type"&&t.text==="ℚ"));
assert(tokenize(samples[2]).some(t=>t.kind==="string"&&t.text.includes("<script>")));
const file=path.resolve(__dirname,"../../comparison/reports/blueprint-statements.json");
const records=JSON.parse(fs.readFileSync(file,"utf8")).declarations;
for(const r of records) {
  const text=r.kind+" "+r.name+":\n"+r.type+(r.value===null?"":" :=\n"+r.value);
  assert.equal(tokenize(text).map(t=>t.text).join(""),text,r.name);
}
console.log("PASS: lossless Lean syntax coloring for "+records.length+" exported declarations, Unicode, nested comments, and HTML-like strings");
