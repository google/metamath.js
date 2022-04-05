const Assert = require("assert");
const nearley = require("nearley");
const compile = require("nearley/lib/compile");
const generate = require("nearley/lib/generate");
const nearleyGrammar = require("nearley/lib/nearley-language-bootstrapped");

describe("Parser", () => {
  function compileGrammar(sourceCode) {
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

  const grammar = compileGrammar(`
      database -> _ outermost_scope_stmt (__ outermost_scope_stmt):* _ {% ([ws1, stmt, list, ws2]) => 
        [stmt].concat(list.map(([ws, v]) => v)) 
      %}

      outermost_scope_stmt -> include_stmt {% id %} | 
                              constant_stmt {% id %} | 
                              stmt {% id %}

      # File inclusion command; process file as a database.
      # Databases should NOT have a comment in the filename.
      include_stmt -> "$[" __ filename __ "$]" {% ([b1, ws1, f, ws2, b2]) => [b1, f, b2] %}

      # Constant symbols declaration.
      constant_stmt -> "$c" __ constant (__ constant):* __ "$." {% ([c, ws1, cons, list, ws2, d]) => 
        [c, [cons].concat(list.map(([ws, v]) => v)), d]
      %}

      # A normal statement can occur in any scope.
      stmt -> block {% id %} | 
              variable_stmt {% id %} | 
              disjoint_stmt {% id %} |
              hypothesis_stmt {% id %} | 
              assert_stmt {% id %}

      # A block. You can have 0 statements in a block.
      block -> "$\{" (__ stmt):* __ "$\}" {% ([b1, list, ws, b2]) => 
        [b1, list.map(([ws, v]) => v), b2] 
      %}

      # Variable symbols declaration.
      variable_stmt -> "$v" __ variable (__ variable):* __ "$." {% ([v, ws1, a, list, ws2, d]) => 
        [v, [a].concat(list.map(([ws, arg]) => arg)), d] 
      %}

      # Disjoint variables. Simple disjoint statements have
      # 2 variables, i.e., "variable*" is empty for them.
      disjoint_stmt -> "$d" variable variable variable:* "$."

      hypothesis_stmt -> floating_stmt {% id %} | essential_stmt {% id %}

      # Floating (variable-type) hypothesis.
      floating_stmt -> LABEL __ "$f" __ typecode __ variable __ "$." {% ([l, ws1, f, ws2, t, ws3, v, ws4, d]) => [l, f, t, v, d] %}

      # Essential (logical) hypothesis.
      essential_stmt -> LABEL __ "$e" __ typecode (__ MATH_SYMBOL):* __ "$." {% ([l, ws1, e, ws2, t, list, ws4, d]) => 
        [l, e, t, list.map(([ws, v]) => v), d] 
      %}

      assert_stmt -> axiom_stmt {% id %} | provable_stmt {% id %}

      # Axiomatic assertion.
      axiom_stmt -> LABEL __ "$a" __ typecode (__ MATH_SYMBOL):* __ "$." {% ([l, ws1, a, ws2, t, list, ws4, d]) => 
        [l, a, t, list.map(([ws, v]) => v), d] 
      %}

      # Provable assertion.
      provable_stmt -> LABEL __ "$p" __ typecode (__ MATH_SYMBOL):* __ "$=" __ proof __ "$." {%
        ([l, ws1, p, ws2, t, list, ws3, eq, ws4, proof, ws5, d]) => 
        [l, p, t, list.map(([ws, v]) => v), eq, proof, d]
      %}

      # A proof. Proofs may be interspersed by comments.
      # If ’?’ is in a proof it’s an "incomplete" proof.
      proof -> uncompressed_proof {% id %} | compressed_proof {% id %}

      uncompressed_proof -> (LABEL | "?") (__ (LABEL | "?")):* {% ([l, list]) => 
        l.concat(list.map(([ws, [v]]) => v)) 
      %}
      compressed_proof -> "(" (__ LABEL):* __ ")" COMPRESSED_PROOF_BLOCK+

      typecode -> constant {% id %}

      filename -> MATH_SYMBOL {% id %}
      constant -> MATH_SYMBOL {% id %}
      variable -> MATH_SYMBOL {% id %}

      # lexicon

      PRINTABLE_SEQUENCE -> _PRINTABLE_CHARACTER:+

      # MATH_SYMBOL -> _PRINTABLE_CHARACTER:+ {% ([str]) => str.join("") %}
      MATH_SYMBOL -> [!-#%-~]:+ {% ([str]) => str.join("") %}

      # ASCII non-whitespace printable characters
      _PRINTABLE_CHARACTER -> [!-~]

      LABEL -> ( _LETTER_OR_DIGIT | "." | "-" | "_" ):+ {% ([str]) => str.join("") %}

      _LETTER_OR_DIGIT -> [A-Za-z0-9]

      COMPRESSED_PROOF_BLOCK -> ([A-Z] | "?"):+

      # Define whitespace between tokens.
      WHITESPACE -> (_WHITECHAR | _COMMENT)

      # Comments. $( ... $) and do not nest.
      _COMMENT -> "$(" (_WHITECHAR:+ [!-#%-~]:+):* _WHITECHAR:+ "$)" _WHITECHAR

      # Whitespace
      _WHITECHAR -> [ \t\\n\v\f] {% id %}

      # Whitespace: _ is optional, __ is mandatory.
      _  -> WHITESPACE:* {% (d) => null %}
      __ -> WHITESPACE:+ {% (d) => null %}

  `);

  function parse(code) {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(code);
    return parser.results;
  }
  
  it("$[ filename $]", () => {    
    assertThat(parse("$[ filename $]"))
      .equalsTo([[
        ["$[", "filename", "$]"]
      ]]);
  });

  it("$( comment $)", () => {    
    assertThat(parse("$( comment $)"))
      .equalsTo([
      ]);
  });

  it("$v a $.", () => {    
    assertThat(parse("$v a $."))
      .equalsTo([[
        ["$v", ["a"], "$."]
      ]]);
  });

  it("$v ab $.", () => {    
    assertThat(parse("$v ab $."))
      .equalsTo([[
        ["$v", ["ab"], "$."]
      ]]);
  });

  it("$v a b $.", () => {    
    assertThat(parse("$v a b $."))
      .equalsTo([[
        ["$v", ["a", "b"], "$."]
      ]]);
  });

  it("$v a b c $.", () => {    
    assertThat(parse("$v a b c $."))
      .equalsTo([[
        ["$v", ["a", "b", "c"], "$."]
      ]]);
  });

  it("$v t r s P Q $.", () => {    
    assertThat(parse("$v t r s P Q $."))
      .equalsTo([[
        ["$v", ["t", "r", "s", "P", "Q",], "$."]
      ]]);
  });

  it("$v a $. $v b $.", () => {    
    assertThat(parse("$v a $. $v b $."))
      .equalsTo([[
        ["$v", ["a"], "$."],
        ["$v", ["b"], "$."]
      ]]);
  });

  it("$c a $.", () => {    
    assertThat(parse("$c a $."))
      .equalsTo([[
        ["$c", ["a"], "$."]
      ]]);
  });

  it("$c a b $.", () => {    
    assertThat(parse("$c a b $."))
      .equalsTo([[
        ["$c", ["a", "b"], "$."]
      ]]);
  });

  it("$c 0 $.", () => {    
    assertThat(parse("$c 0 $."))
      .equalsTo([[
        ["$c", ["0"], "$."]
      ]]);
  });

  it("$c + $.", () => {    
    assertThat(parse("$c + $."))
      .equalsTo([[
        ["$c", ["+"], "$."]
      ]]);
  });

  it("$c = $.", () => {    
    assertThat(parse("$c = $."))
      .equalsTo([[
        ["$c", ["="], "$."]
      ]]);
  });

  it("$c -> $.", () => {    
    assertThat(parse("$c -> $."))
      .equalsTo([[
        ["$c", ["->"], "$."]
      ]]);
  });

  it("$c 0 + = -> ( ) term wff |- $.", () => {    
    assertThat(parse("$c 0 + = -> ( ) term wff |- $."))
      .equalsTo([[
        ["$c", ["0", "+", "=", "->", "(", ")", "term", "wff", "|-"], "$."]
      ]]);
  });

  it("tt $f term t $.", () => {    
    assertThat(parse("tt $f term t $."))
      .equalsTo([[
        ["tt", "$f", "term", "t", "$."]
      ]]);
  });

  it("weq $a wff t $.", () => {    
    assertThat(parse("weq $a wff t $."))
      .equalsTo([[
        ["weq", "$a", "wff", ["t"], "$."]
      ]]);
  });

  it("weq $a wff t u $.", () => {    
    assertThat(parse("weq $a wff t u $."))
      .equalsTo([[
        ["weq", "$a", "wff", ["t", "u"], "$."]
      ]]);
  });

  it("weq $a wff t = r $.", () => {    
    assertThat(parse("weq $a wff t = r $."))
      .equalsTo([[
        ["weq", "$a", "wff", ["t", "=", "r"], "$."]
      ]]);
  });

  it("wim $a wff ( P -> Q ) $.", () => {    
    assertThat(parse("wim $a wff ( P -> Q ) $."))
      .equalsTo([[
        ["wim", "$a", "wff", ["(", "P", "->", "Q", ")"], "$."]
      ]]);
  });
  
  it("a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.", () => {    
    assertThat(parse("a1 $a |- ( t = r -> ( t = s -> r = s ) ) $."))
      .equalsTo([[
        ["a1", "$a", "|-", ["(", "t", "=", "r", "->", "(", "t", "=", "s", "->", "r", "=", "s", ")", ")"], "$."]
      ]]);
  });

  it("a2 $a |- ( t + 0 ) = t $.", () => {    
    assertThat(parse("a2 $a |- ( t + 0 ) = t $."))
      .equalsTo([[
        ["a2", "$a", "|-", ["(", "t", "+", "0", ")", "=", "t"], "$."]
      ]]);
    });

  it("${ $}", () => {
    assertThat(parse("${ $}"))
      .equalsTo([[
        ["${", [], "$}"]
      ]]);
  });

  it("${  $}", () => {
    assertThat(parse("${  $}"))
      .equalsTo([[
        ["${", [], "$}"]
      ]]);
  });

  it("min $e |- P $.", () => {    
    assertThat(parse("min $e |- P $."))
      .equalsTo([[
        ["min", "$e", "|-", ["P"], "$."]
      ]]);
  });

  it("maj $e |- ( P -> Q ) $.", () => {    
    assertThat(parse("maj $e |- ( P -> Q ) $."))
      .equalsTo([[
        ["maj", "$e", "|-", ["(", "P", "->", "Q", ")"], "$."]
      ]]);
    });

  it("${ min $e |- P $. $}", () => {    
    assertThat(parse("${ min $e |- P $. $}"))
      .equalsTo([[
        ["${", [
          ["min", "$e", "|-", ["P"], "$."]
        ], "$}"]
      ]]);
    });

  it("${ min $e |- P $. maj $e |- ( P -> Q ) $. $}", () => {    
    assertThat(parse("${ min $e |- P $. maj $e |- ( P -> Q ) $. $}"))
      .equalsTo([[
        ["${", [
          ["min", "$e", "|-", ["P"], "$."],
          ["maj", "$e", "|-", ["(", "P", "->", "Q", ")"], "$."],          
        ], "$}"]
      ]]);
    });

  it("th1 $p |- t = t $= tt tze $.", () => {    
    assertThat(parse("th1 $p |- t = t $= tt tze $."))
      .equalsTo([[
        ["th1", "$p", "|-", ["t", "=", "t"], "$=", ["tt", "tze"], "$."]
      ]]);
    });

  it("$c M I U |- wff $. $( Declare constants $)", () => {
    assertThat(parse(`
      $c M I U |- wff $. $( Declare constants $)
    `)).equalsTo([[
      ["$c", ["M", "I", "U", "|-", "wff"], "$."]
    ]]);
  });
  
  it("$( $) $( $) $c a $.", () => {
    assertThat(parse(`
      $( $)
      $( $)
      $c a $.
    `)).equalsTo([[
      ["$c", ["a"], "$."]
    ]]);
  });
  
  it("$c a $. we $a wff $.", () => {
    assertThat(parse(`
      $c a $.
      we $a wff $.
    `)).equalsTo([[
      ["$c", ["a"], "$."],
      ["we", "$a", "wff", [], "$."]
    ]]);
  });

  it("P -> Q. P. |- Q.", () => {
    assertThat(parse(`
      $( P, Q and R are variables $)
      $v P Q R $.

      $( "->", "(", ")", "|-" and "wff" are tokens $)
      $c -> ( ) |- wff $.

      $( P is a wff $)
      wp $f wff P $.

      $( Q is a wff $)
      wq $f wff Q $.

      $( major premise: P -> Q $)
      maj $e |- ( P -> Q ) $.

      $( minor premise: P $)
      min $e |- P $.

      $( consequent $)
      mp $a |- Q $.
    `)).equalsTo([[
      ["$v", ["P", "Q", "R"], "$."],
      ["$c", ["->", "(", ")", "|-", "wff"], "$."],
      ["wp", "$f", "wff", "P", "$."],
      ["wq", "$f", "wff", "Q", "$."],
      ["maj", "$e", "|-", ["(", "P", "->", "Q", ")"], "$."],      
      ["min", "$e", "|-", ["P"], "$."],      
      ["mp", "$a", "|-", ["Q"], "$."],      
    ]]);
  });

  it("MIU", () => {    
    assertThat(parse(`
      $( miu.mm  20-Oct-2008 $)

      $( The MIU-system:  A simple formal system $)

      $( First, we declare the constant symbols of the language.
         Note that we need two symbols to distinguish the assertion
         that a sequence is a wff from the assertion that it is a
         theorem; we have arbitrarily chosen "wff" and "|-". $)

       $c M I U |- wff $. $( Declare constants $)

       $( Next, we declare some variables. $)

       $v x y $.

       $( Throughout our theory, we shall assume that these
          variables represent wffs. $)

       wx $f wff x $.
       wy $f wff y $.

       $( Define MIU-wffs.  We allow the empty sequence to be a
          wff. $)

       $( The empty sequence is a wff. $)
       we $a wff $.

       $( "M" after any wff is a wff. $)
       wM $a wff x M $.

       $( "I" after any wff is a wff. $)
       wI $a wff x I $.

       $( "U" after any wff is a wff. $)
       wU   $a wff x U $.

       $( If "x" and "y" are wffs, so is "x y".  This allows the conclusion of
       IV to be provable as a wff before substitutions into it, for those
       parsers requiring it.  (Added per suggestion of Mel O'Cat 4-Dec-04.) $)
       wxy  $a wff x y $.

       $( Assert the axiom. $)
       ax   $a |- M I $.

       $( Assert the rules. $)
       $\{ 
         Ia   $e |- x I $.

         $( Given any theorem ending with "I", it remains a theorem
            if "U" is added after it.  (We distinguish the label I_
            from the math symbol I to conform to the 24-Jun-2006
            Metamath spec change.) $)
            I_    $a |- x I U $.
       $\}

       $\{
         IIa  $e |- M x $.
         $( Given any theorem starting with "M", it remains a theorem
           if the part after the "M" is added again after it. $)
         II   $a |- M x x $.
       $\}

       $\{
         IIIa $e |- x I I I y $.
         $( Given any theorem with "III" in the middle, it remains a
           theorem if the "III" is replace with "U". $)
         III  $a |- x U y $.
       $\}

       $\{
         IVa  $e |- x U U y $.
         $( Given any theorem with "UU" in the middle, it remains a
           theorem if the "UU" is deleted. $)
         IV   $a |- x y $.
       $\}

       $( Now we prove the theorem MUIIU.  You may be interested in
          comparing this proof with that of Hofstadter (pp. 35 - 36). $)
       theorem1  $p |- M U I I U $=
         we wM wU wI we wI wU we wU wI wU we wM we wI wU we wM
         wI wI wI we wI wI we wI ax II II I_ III II IV $.
    `))
      .equalsTo([[
        ["$c", ["M", "I", "U", "|-", "wff"], "$."],
        ["$v", ["x", "y"], "$."],
        ["wx", "$f", "wff", "x", "$."],
        ["wy", "$f", "wff", "y", "$."],
        ["we", "$a", "wff", [], "$."],
        ["wM", "$a", "wff", ["x", "M"], "$."],
        ["wI", "$a", "wff", ["x", "I"], "$."],        
        ["wU", "$a", "wff", ["x", "U"], "$."],        
        ["wxy", "$a", "wff", ["x", "y"], "$."],        
        ["ax", "$a", "|-", ["M", "I"], "$."],
        ["${", [
          ["Ia", "$e", "|-", ["x", "I"], "$."],
          ["I_", "$a", "|-", ["x", "I", "U"], "$."],
        ], "$}"],
        ["${", [
          ["IIa", "$e", "|-", ["M", "x"], "$."],
          ["II", "$a", "|-", ["M", "x", "x"], "$."],
        ], "$}"],
        ["${", [
          ["IIIa", "$e", "|-", ["x", "I", "I", "I", "y"], "$."],
          ["III", "$a", "|-", ["x", "U", "y"], "$."],
        ], "$}"],
        ["${", [
          ["IVa", "$e", "|-", ["x", "U", "U", "y"], "$."],
          ["IV", "$a", "|-", ["x", "y"], "$."],
        ], "$}"],
        ["theorem1", "$p", "|-", ["M", "U", "I", "I", "U"], "$=", [
          "we", "wM", "wU", "wI", "we", "wI", "wU", "we", "wU", "wI",
          "wU", "we", "wM", "we", "wI", "wU", "we", "wM", "wI", "wI",
          "wI", "we", "wI", "wI", "we", "wI", "ax", "II", "II", "I_",
          "III", "II", "IV"
        ], "$."],
      ]]);
    });

  it("( s -> ( r -> p ) )", () => {
    assertThat(parse(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `)).equalsTo([[
      ["$c", ["(", ")", "->", "wff"], "$."],
      ["$v", ["p", "q", "r", "s"], "$."],
      ["wp", "$f", "wff", "p", "$."],
      ["wq", "$f", "wff", "q", "$."],
      ["wr", "$f", "wff", "r", "$."],
      ["ws", "$f", "wff", "s", "$."],
      ["w2", "$a", "wff", ["(", "p", "->", "q", ")"], "$."],
      ["wnew", "$p", "wff", ["(", "s", "->", "(", "r", "->", "p",  ")", ")"], "$=",
       ["ws", "wr", "wp", "w2", "w2"],
       "$."],
    ]]);
  });
  
  it("( s -> ( r -> p ) )", () => {
    const [code] = parse(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `);

    const constants = [];
    const variables = [];
    const hypothesis = {};
    const axioms = {};
    const theorems = {};

    const labels = {};
    
    for (const stmt of code) {
      const [first, second] = stmt;
      if (first == "$c") {
        const [, vars] = stmt;
        constants.push(...vars);
      } else if (first == "$v") {
        const [, vars] = stmt;        
        variables.push(...vars);
      } else if (second == "$f") {
        const [label, f, type, variable] = stmt;
        hypothesis[variable] = label;
        labels[label] = [f, [type, variable]];
      } else if (second == "$a") {
        const [label, a, types, rule] = stmt;
        const mandatory = rule
              .filter((r) => variables.includes(r))
              .map((r) => {
                if (!hypothesis[r]) throw new Error(`Unknown variable type: ${r}`);
                return hypothesis[r]
              });

        mandatory.reverse();
        axioms[label] = [types, rule, mandatory];
        labels[label] = [a, stmt];
      } else if (second == "$p") {
        const [label, p, types, theorem, d, proof] = stmt;
        const mandatory = theorem
              .filter((r) => variables.includes(r))
              .map((r) => {
                if (!hypothesis[r]) throw new Error(`Unknown variable type: ${r}`);
                return hypothesis[r]
              });

        const stack = [];
        
        for (const step of proof) {
          const [type] = labels[step];
          if (type == "$f") {
            const [, [type, variable]] = labels[step];
            stack.push([type, variable]);
          } else if (type == "$a") {
            const [t, head, hypothesis] = axioms[step];
            const unify = {};
            for (const h of hypothesis) {
              const [, [type, name]] = labels[h];
              if (stack.length == 0) {
                throw new Error("Unify failed: empty stack.");
              }
              const [k, arg] = stack.pop();
              if (k != type) {
                throw new Error(`Types don't match ${k} != ${type}`);
              }
              unify[name] = arg;
            }
            const sub = head.map((arg) => unify[arg] || arg);
            stack.push([t, sub.flat()]);
          }
        }

        if (stack.length != 1) {
          throw new Error(`Proof Error: Stack is not empty`);
        }

        const result = stack[0];

        if (result[0] != types) {
          throw new Error(`Proof Error: Resulting type doesn't match ${result[0]} != ${types}`);
        }

        if (result[1].join("") !== theorem.join("")) {
          throw new Error(`Proof Error: Resulting theorem doesn't match ${result[1].join("")} != ${theorem.join("")}`);
        }

        theorems[label] = [types, theorem, mandatory, proof];
      }
    }

    assertThat(constants)
      .equalsTo(["(", ")", "->", "wff"]);
    assertThat(variables)
      .equalsTo(["p", "q", "r", "s"]);
    assertThat(hypothesis)
      .equalsTo({"p": "wp", "q": "wq", "r": "wr", "s": "ws"});
    assertThat(axioms)
      .equalsTo({"w2": [
        "wff",
        ["(", "p", "->", "q", ")"],
        ["wq", "wp"]
      ]});
    assertThat(theorems)
      .equalsTo({"wnew": [
        "wff",
        ["(", "s", "->", "(", "r", "->", "p", ")", ")"],
        ["ws", "wr", "wp"],
        ["ws", "wr", "wp", "w2", "w2"]
      ]});
  });

});


function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
