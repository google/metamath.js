const nearley = require("nearley");
const compile = require("nearley/lib/compile");
const generate = require("nearley/lib/generate");
const nearleyGrammar = require("nearley/lib/nearley-language-bootstrapped");

const {lexer} = require("./lexer.js");

function compileGrammar(handler = false, sourceCode) {
  // Parse the grammar source into an AST
  const grammarParser = new nearley.Parser(nearleyGrammar);
  grammarParser.feed(sourceCode);
  const grammarAst = grammarParser.results[0]; // TODO check for errors
      
  // Compile the AST into a set of rules
  const grammarInfoObject = compile(grammarAst, {});
  // Generate JavaScript code from the rules
  const grammarJs = generate(grammarInfoObject, "grammar");
      
  // Pretend this is a CommonJS environment to catch exports from the grammar.
  const module = { exports: {} };

  eval(grammarJs);

  return module.exports;
}

//const handler = true;

const grammar = (handler) => compileGrammar(handler, `
      @lexer lexer

      #database -> _ outermost_scope_stmt (__ outermost_scope_stmt):* _ {% ([ws1, stmt, list, ws2]) =>
      #  [stmt].concat(list.map(([ws, v]) => v)) 
      #%}

      database -> _ __aline_plus _ {% ([ws, lines]) => lines %}

      __aline_plus -> outermost_scope_stmt {%
            ([line]) => {
              if (handler) {
                handler.feed([line]);
                return null;
              }
              return [line];
            }
           %} |
           __aline_plus __ outermost_scope_stmt {%
             ([prior, ws, next]) => {
               if (handler) {
                 handler.feed([next]);
                 return null;
               }
               return [...prior, next];
             }
          %}

      outermost_scope_stmt -> include_stmt {% id %} | 
                              constant_stmt {% id %} | 
                              stmt {% id %}

      # File inclusion command; process file as a database.
      # Databases should NOT have a comment in the filename.
      include_stmt -> %lfile  __ filename __ %rfile {% ([b1, ws1, f, ws2, b2]) => [b1.text, f.text, b2.text] %}

      # Constant symbols declaration.
      constant_stmt -> %c __ constant (__ constant):* __ %dot {% ([c, ws1, cons, list, ws2, d]) => 
        [c.text, [cons.text].concat(list.map(([ws, v]) => v.text)), d.text]
      %}

      # A normal statement can occur in any scope.
      stmt -> block {% id %} | 
              variable_stmt {% id %} | 
              disjoint_stmt {% id %} |
              hypothesis_stmt {% id %} | 
              assert_stmt {% id %}

      # A block. You can have 0 statements in a block.
      block -> %lscope (__ stmt):* __ %rscope {% ([b1, list, ws, b2]) => 
        [b1.text, list.map(([ws, v]) => v), b2.text] 
      %}

      # Variable symbols declaration.
      variable_stmt -> %v __ variable (__ variable):* __ %dot {% ([v, ws1, a, list, ws2, d]) => 
        [v.text, [a.text].concat(list.map(([ws, arg]) => arg.text)), d.text] 
      %}

      # Disjoint variables. Simple disjoint statements have
      # 2 variables, i.e., "variable*" is empty for them.
      disjoint_stmt -> %d __ variable (__ variable):* __ %dot {% ([v, ws1, a, list, ws2, d]) =>
        [v.text, [a.text].concat(list.map(([ws, arg]) => arg.text)), d.text]
      %}

      hypothesis_stmt -> floating_stmt {% id %} | essential_stmt {% id %}

      # Floating (variable-type) hypothesis.
      floating_stmt -> LABEL __ %f __ typecode __ variable __ %dot {% ([l, ws1, f, ws2, t, ws3, v, ws4, d]) => [l, f.text, t.text, v.text, d.text] %}

      # Essential (logical) hypothesis.
      essential_stmt -> LABEL __ %e __ typecode (__ MATH_SYMBOL):* __ %dot {% ([l, ws1, e, ws2, t, list, ws4, d]) => 
        [l, e.text, t.text, list.map(([ws, v]) => v.text), d.text] 
      %}

      assert_stmt -> axiom_stmt {% id %} | provable_stmt {% id %}

      # Axiomatic assertion.
      axiom_stmt -> LABEL __ %a __ typecode (__ MATH_SYMBOL):* __ %dot {% ([l, ws1, a, ws2, t, list, ws4, d]) => 
        [l, a.text, t.text, list.map(([ws, v]) => v.text), d.text] 
      %}

      # Provable assertion.
      provable_stmt -> LABEL __ %p __ typecode (__ MATH_SYMBOL):* __ %proof __ proof __ %dot {%
        ([l, ws1, p, ws2, t, list, ws3, eq, ws4, proof, ws5, d]) => 
        [l, p.text, t.text, list.map(([ws, v]) => v.text), eq.text, proof, d.text]
      %}

      # A proof. Proofs may be interspersed by comments.
      # If ’?’ is in a proof it’s an "incomplete" proof.
      proof -> uncompressed_proof {% id %} | compressed_proof {% id %}

      uncompressed_proof -> (LABEL | "?") (__ (LABEL | "?")):* {% ([l, list]) => 
        l.concat(list.map(([ws, [v]]) => v)) 
      %}

      compressed_proof -> "("  (__ LABEL):* __ ")" __ COMPRESSED_PROOF_BLOCK
      {% 
        ([p1, labels, ws1, p2, ws2, proof]) => 
         [p1.text, labels.map(([ws, l]) => l), p2.text, proof] 
      %}

      typecode -> constant {% id %}
      filename -> MATH_SYMBOL {% id %}
      constant -> MATH_SYMBOL {% id %}
      variable -> MATH_SYMBOL {% id %}

      MATH_SYMBOL -> %sequence {% id %}

      # lexicon

      LABEL -> ( _LETTER_OR_DIGIT | "." | "-" | "_" ):+ {% ([str]) => str.join("") %}

      _LETTER_OR_DIGIT -> %sequence {% ([a], loc, r) => { return a.text.match(/[A-Za-z0-9]/) ? a : r } %}

      COMPRESSED_PROOF_BLOCK -> ([A-Z] | "?" | %ws):+ {% ([a]) => a.join("") %}

      # Define whitespace between tokens.
      WHITESPACE -> (%ws | %comment)

      # Whitespace: _ is optional, __ is mandatory.
      _  -> WHITESPACE:* {% (d) => null %}
      __ -> WHITESPACE:+ {% (d) => null %}
`);

function parse(code, handler = false) {
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(handler)));
  parser.feed(code);
  return parser.results;
}

module.exports = {
  parse: parse,
  grammar: grammar,
};
