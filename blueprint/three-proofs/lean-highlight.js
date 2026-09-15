/* Lexical Lean highlighting. Never evaluates code or changes the exported text.
 * Nested comments, Unicode identifiers, escaped names, and strings are preserved.
 * This is syntax coloring, not a substitute for Lean's semantic elaboration. */
(function (root) {
  'use strict';
  const keywords = new Set(('theorem lemma def abbrev opaque axiom constant inductive structure class instance ' +
    'where by fun forall exists let in if then else match with do return have show from ' +
    'exact apply intro intros constructor cases induction obtain refine rw simp simpa ' +
    'namespace end open import variable variables universe universes noncomputable ' +
    'private protected unsafe partial mutual deriving attribute set_option ' +
    'termination_by decreasing_by sorry admit').split(' '));
  const declarations = new Set('theorem lemma def abbrev opaque axiom constant inductive structure class'.split(' '));
  const types = new Set('Prop Type Sort Rat Real RealRaw QInterval QPos Nat Int Bool String List Array Option Set Finset Complex ℕ ℤ ℚ ℝ ℂ'.split(' '));
  const ident = /^[\p{L}\p{Nl}_][\p{L}\p{N}\p{M}_'’!?]*(?:\.[\p{L}\p{Nl}_][\p{L}\p{N}\p{M}_'’!?]*)*/u;
  const number = /^(?:0[xX][0-9a-fA-F]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)/u;
  const operator = /^(?::=|=>|->|<-|::|==|!=|<=|>=|[∀∃λ→←↔⇒⟨⟩≤≥≠∧∨¬∈∉⊆⊂∪∩⊢×⁻¹+*/=<>:^|&!~−-])/u;

  function tokenize(text) {
    const result = [];
    let i = 0, expectName = false;
    function emit(end, kind) {
      result.push({text: text.slice(i, end), kind}); i = end;
    }
    while (i < text.length) {
      const rest = text.slice(i);
      if (rest.startsWith('/-')) {
        let j = i + 2, depth = 1;
        while (j < text.length && depth) {
          if (text.startsWith('/-', j)) { depth++; j += 2; }
          else if (text.startsWith('-/', j)) { depth--; j += 2; }
          else j++;
        }
        emit(j, 'comment'); continue;
      }
      if (rest.startsWith('--')) {
        const end = text.indexOf('\n', i); emit(end < 0 ? text.length : end, 'comment'); continue;
      }
      if (rest[0] === '"') {
        let j = i + 1;
        while (j < text.length) {
          if (text[j] === '\\') { j = Math.min(j + 2, text.length); continue; }
          if (text[j++] === '"') break;
        }
        emit(j, 'string'); continue;
      }
      if (rest[0] === '«') {
        const end = text.indexOf('»', i + 1);
        emit(end < 0 ? text.length : end + 1, expectName ? 'declaration' : 'identifier');
        expectName = false; continue;
      }
      const char = rest.match(/^'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'/u);
      if (char) { emit(i + char[0].length, 'string'); continue; }
      const word = rest.match(ident);
      if (word) {
        const value = word[0], last = value.split('.').pop();
        const kind = keywords.has(value) ? 'keyword' : expectName ? 'declaration' : types.has(last) ? 'type' : null;
        if (declarations.has(value)) expectName = true;
        else if (!keywords.has(value)) expectName = false;
        emit(i + value.length, kind); continue;
      }
      const literal = rest.match(number);
      if (literal) { emit(i + literal[0].length, 'number'); continue; }
      const op = rest.match(operator);
      if (op) { emit(i + op[0].length, 'operator'); continue; }
      const space = rest.match(/^\s+/u);
      emit(i + (space ? space[0].length : String.fromCodePoint(text.codePointAt(i)).length), null);
    }
    return result;
  }

  function highlight(code) {
    const original = code.textContent, fragment = document.createDocumentFragment();
    for (const token of tokenize(original)) {
      if (token.kind) {
        const span = document.createElement('span'); span.className = 'lean-token lean-' + token.kind;
        span.textContent = token.text; fragment.append(span);
      } else fragment.append(document.createTextNode(token.text));
    }
    code.replaceChildren(fragment);
    if (code.textContent !== original) throw new Error('Lean highlighting changed the statement');
    code.classList.add('language-lean');
    return code;
  }
  const api = {tokenize, highlight};
  root.LeanSnippet = api;
  if (typeof module === 'object' && module.exports) module.exports = api;
})(typeof globalThis !== 'undefined' ? globalThis : this);
