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
      compressed_proof -> "(" (__ LABEL):* __ ")" __ COMPRESSED_PROOF_BLOCK
      {% 
        ([p1, labels, ws1, p2, ws2, proof]) => 
         [p1, labels.map(([ws, l]) => l), p2, proof] 
      %}

      typecode -> constant {% id %}

      filename -> MATH_SYMBOL {% id %}
      constant -> MATH_SYMBOL {% id %}
      variable -> MATH_SYMBOL {% id %}

      # lexicon

      PRINTABLE_SEQUENCE -> _PRINTABLE_CHARACTER:+ {% ([str]) => str.join("") %}

      # MATH_SYMBOL -> _PRINTABLE_CHARACTER:+ {% ([str]) => str.join("") %}
      MATH_SYMBOL -> [!-#%-~]:+ {% ([str]) => str.join("") %}

      # ASCII non-whitespace printable characters
      _PRINTABLE_CHARACTER -> [!-~]

      LABEL -> ( _LETTER_OR_DIGIT | "." | "-" | "_" ):+ {% ([str]) => str.join("") %}

      _LETTER_OR_DIGIT -> [A-Za-z0-9]

      COMPRESSED_PROOF_BLOCK -> ([A-Z] | "?"):+ {% ([a]) => a.join("") %}

      # Define whitespace between tokens.
      WHITESPACE -> (_WHITECHAR | _COMMENT)

      # Comments. $( ... $) and do not nest.
      # TODO(goto): the BNF doesn't accept "$" in comments, but set.mm seems to use them.
      _COMMENT -> "$(" (_WHITECHAR:+ PRINTABLE_SEQUENCE):* _WHITECHAR:+ "$)" _WHITECHAR {%
        ([l, comment], loc, reject) => {
          for (let [, word] of comment) {
            // Reject PRINTABLE_SEQUENCEs that have "$)" in them.
            if (word == "$)") {
              return reject;
            }
          }
          return null;
        }
      %}

      # Whitespace
      _WHITECHAR -> [ \t\\n\v\f] {% id %}

      # Whitespace: _ is optional, __ is mandatory.
      _  -> WHITESPACE:* {% (d) => null %}
      __ -> WHITESPACE:+ {% (d) => null %}

  `);

  function parse(code, first = false) {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(code);
    return first ? parser.results[0] : parser.results;
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

  it("$( comment $f $)", () => {    
    assertThat(parse("$( comment $f $)"))
      .equalsTo([
      ]);
  });

  it("$( $) $( $) $c a $.", () => {
    assertThat(parse(`
      $( ab cd $)
      $( ef gh $)
      $c a $.
    `)).equalsTo([[
      ["$c", ["a"], "$."]
    ]]);
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

  it("${ $v a $. $}", () => {
    assertThat(parse("${ $v a $. $}"))
      .equalsTo([[
        ["${", [
          ["$v", ["a"], "$."]
        ], "$}"]
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
      $( a $)
      $( b $)
      $c a $.
    `)).equalsTo([[
      ["$c", ["a"], "$."]
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

  it("mp2 $p |- ch $= ( wi ax-mp ) BCEABCGDFHH $.", () => {
    assertThat(parse(`
      mp2 $p |- ch $= ( wi ax-mp ) BCEABCGDFHH $.
    `)).equalsTo([[
      ["mp2", "$p", "|-", ["ch"], "$=", ["(", ["wi", "ax-mp"], ")", "BCEABCGDFHH"], "$."]
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

  function frame(code) {
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
          //console.log(step);
          //console.log(labels);
          if (!labels[step]) {
            throw new Error(`Unknown label in proof ${step}.`);
          }
          const [type] = labels[step];
          if (type == "$f") {
            const [, [type, variable]] = labels[step];
            stack.push([type, variable]);
          } else if (type == "$a" || type == "$p") {
            const [t, head, hypothesis] = type == "$a" ? axioms[step] : labels[step][1];
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
          } else if (type == "$p") {
            const [p, [t, hypothesis, head]] = labels[step];
            const unify = {};
            for (const h of hypothesis) {
              // console.log(h);
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
          } else {
            throw new Error(`Unknown label type ${type}.`);
          }

        }
        
        if (stack.length != 1) {
          console.log(stack);
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

        labels[label] = ["$p", [types, theorem, mandatory]];
      }
    }

    return [constants, variables, hypothesis, axioms, theorems];
  }
  
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

    const [constants, variables, hypothesis, axioms, theorems] = frame(code);
    
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

  it("propositional logic", () => {
    const [code] = parse(`
      $c ( ) -> wff ~ $.
      $v p q r $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      wi $a wff ( p -> q ) $.
      wn $a wff ~ p $.
      ax-1 $a wff ( p -> ( q -> p ) ) $.
      ax-2 $a wff ( ( p -> ( q -> r ) ) -> ( ( p -> q ) -> ( p -> r ) ) ) $.
      ax-3 $a wff ( ( ~ p -> ~ q ) -> ( q -> p ) ) $.
    `);

    const result = frame(code);

  });
  
  it("mmverify.py", () => {
    const stack = new Stack();
    stack.push();

    assertThat(stack.lookupC("a")).equalsTo(false);

    stack.addC("a");
    try {
      stack.addC("a");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo("const already declared in scope");
    }

    assertThat(stack.lookupC("a")).equalsTo(true);

    try {
      stack.addV("a");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo("var already declared as a const in scope");
    }

    assertThat(stack.lookupV("b")).equalsTo(false);

    stack.addV("b");
    try {
      stack.addV("b");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo("var already declared in scope");
    }

    assertThat(stack.lookupV("b")).equalsTo(true);
    
    try {
      stack.addC("b");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo("const already declared as a var in scope");
    }

    stack.addF("b", "a", "foo");

    assertThat(stack.top().f).equalsTo([["b", "a"]]);
    assertThat(stack.top().f_labels).equalsTo({"b": "foo"});

    try {
      stack.addF("c", "a", "foo");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo(`var "c" in $f not defined.`);
    }

    try {
      stack.addF("b", "c", "foo");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo(`const in $f not defined: c.`);
    }

    try {
      stack.addF("b", "a", "foo");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo(`var b in $f already defined in scope`);
    }

    assertThat(stack.lookupF("b")).equalsTo("foo");
    
    try {
      stack.lookupF("bar");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo(`Unknown $f key: bar.`);
    }

    stack.addE(["bar"], "|-", "foo");
    assertThat(stack.lookupE([["bar"], "|-"])).equalsTo("foo");

    try {
      stack.lookupE("hello");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo(`Unknown $e key: hello.`);
    }

    assertThat(stack.assert("foo", "bar"))
      .equalsTo([
        [],
        [["a", "b"]],
        [[["bar"], "|-"]],
        ["foo", "bar"]
      ]);

    //assertThat(new MM().read(parse(`
    //    wi $a wff ( p -> q ) $.
    //`, true)).labels["wi"])
    //  .equalsTo(true);

    //assertThat(new MM().read(parse(`
    //  min $e wff ph $.
    //  maj $e wff ( ph -> ps ) $.
    //  ax-mp $a wff ps $.
    //`, true)).frames.top().e)
    //  .equalsTo(new Set(["b"]));

    //assertThat(new MM().read(parse(`
    //  wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    //`, true)).frames.top().e)
    //  .equalsTo(new Set(["b"]));


  });

  it("$c a $.", () => {
    assertThat(new MM().read(parse(`
      $c a $.
    `, true)).c)
      .equalsTo(new Set(["a"]));
  });
  
  it("$v b $.", () => {
    assertThat(new MM().read(parse(`
      $v b $.
    `, true)).v)
      .equalsTo(new Set(["b"]));
  });
  
  it("$c a $. $v b $.", () => {
    assertThat(new MM().read(parse(`
        $c a $.
        $v b $.
    `, true)).c)
      .equalsTo(new Set(["a"]));
  });
  
  it("$c a $. $v b $.", () => {
    assertThat(new MM().read(parse(`
        $c a $.
        $v b $.
    `, true)).v)
      .equalsTo(new Set(["b"]));
  });
  
  it("${ $v a b c $. $}", () => {
    assertThat(new MM().read(parse(`
      $\{
        $v a b c $.
      $\}
    `, true)).v)
      .equalsTo(new Set([]));
    // The top frame has no variables.
  });
  
  it("w2 $a wff ( p -> q ) $.", () => {
    const mm = new MM();
    mm.read(parse(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
    `, true));
    assertThat(mm.labels["w2"])
      .equalsTo(["$a", [
        [],
        [["wff", "p"], ["wff", "q"]],
        [],
        ["wff", ["(", "p", "->", "q", ")"]]
      ]]);
  });
  
  class Frame {
    constructor() {
      this.c = new Set();
      this.v = new Set();
      this.d = new Set();
      this.f = [];
      this.f_labels = {};
      this.e = [];
      this.e_labels = {};
    }
  }
  
  class Stack {
    constructor() {
      this.stack = [];
    }
    
    push() {
      const top = new Frame();
      this.stack.push(top);
      return top;
    }

    pop() {
      return this.stack.pop();
    }

    top() {
      return this.stack[this.stack.length - 1];
    }
    
    addC(tok) {
      const frame = this.top();
      
      if (frame.c.has(tok)) {
        throw new Error("const already declared in scope");
      }
      
      if (frame.v.has(tok)) {
        throw new Error("const already declared as a var in scope");
      }
      
      frame.c.add(tok);
    }

    addV(tok) {
      const frame = this.top();
      
      if (frame.v.has(tok)) {
        throw new Error("var already declared in scope");
      }
      
      if (frame.c.has(tok)) {
        throw new Error("var already declared as a const in scope");
      }

      frame.v.add(tok);
    }

    lookupV(tok) {
      for (const frame of [...this.stack].reverse()) {
        if (frame.v.has(tok)) {
          return true;
        }
      }
      return false;
    }
    
    lookupC(tok) {
      for (const frame of [...this.stack].reverse()) {
        if (frame.c.has(tok)) {
          return true;
        }
      }
      return false;
    }
      
    addF(varz, kind, label) {
      if (!this.lookupV(varz)) {
        throw new Error(`var "${varz}" in $f not defined.`);
      }
      if (!this.lookupC(kind)) {
        throw new Error(`const in $f not defined: ${kind}.`);
      }
      
      const frame = this.top();
      
      if (Object.keys(frame.f_labels).includes(varz)) {
        throw new Error(`var ${varz} in $f already defined in scope`);
      }

      frame.f.push([varz, kind]);
      frame.f_labels[varz] = label;
    }
    
    addE(rule, kind, label) {
      const frame = this.top();
      frame.e.push([rule, kind]);
      const tag = [rule, kind].flat().join("");
      frame.e_labels[tag] = label;
    }

    addD(stat) {
      const frame = this.top();
    }

    lookupF(varz) {
      for (const frame of [...this.stack].reverse()) {
        if (frame.f_labels[varz]) {
          return frame.f_labels[varz];
        }
      }
      throw new Error(`Unknown $f key: ${varz}.`);
    }

    lookupE(rule, kind) {
      const tag = [rule, kind].flat().join("");
      for (const frame of [...this.stack].reverse()) {
        if (frame.e_labels[tag]) {
          return frame.e_labels[tag];
        }
      }        
      throw new Error(`Unknown $e key: ${tag}.`);
    }

    assert(type, rule) {
      const frame = this.top();
      const e = this.stack
            .map((frame) => frame.e)
            .flat();

      const mandatory = new Set();
      
      for (const [hyp] of [...e, [rule, type]]) {
        // console.log(hyp);
        for (const tok of hyp) {
          if (this.lookupV(tok)) {
            mandatory.add(tok);
          }
        }
      }

      // TODO: deal with distinct variables.
      const dvs = [];
      
      const f = [];

      // console.log(mandatory);
      for (const frame of [...this.stack].reverse()) {
        for (const [v, k] of [...frame.f].reverse()) {
          // console.log(`${v} ${k}`);
          if (mandatory.has(v)) {
            f.unshift([k, v]);
            mandatory.delete(v);
          }
        }
      }

      return [dvs, f, e, [type, rule]];
    }
  }

  it("assert()", () => {
    const stack = new Stack();
    stack.push();
    stack.addC("A");
    stack.addC("~");
    assertThat(stack.top().c).equalsTo(new Set(["A", "~"]));
    stack.addV("a");
    stack.addV("b");
    stack.addV("c");
    assertThat(stack.top().v).equalsTo(new Set(["a", "b", "c"]));
    assertThat(stack.lookupV("a"));
    // Variable a is of type A.
    stack.addF("a", "A", "let1");
    assertThat(stack.lookupF("a"))
      .equalsTo("let1");

    // Enter a new frame.
    stack.push();
    // There is a variable "d" of type A.
    stack.addF("c", "A", "let2");
    // There is another variable, "a", which was declared earlier,
    // and it must be false.
    stack.addE(["~", "a"], "|-", "hypothesis");
    assertThat(stack.lookupE(["~", "a"], "|-"))
      .equalsTo("hypothesis");
    // If the hypothesis match, "b" implies "c".
    const [, mand, hyps] = stack.assert("A", ["b", "->", "c"]);
    assertThat(mand).equalsTo([
      ["A", "a"],
      ["A", "c"],
    ]);
    assertThat(hyps).equalsTo([[["~", "a"], "|-"]]);
    stack.pop();

    stack.pop();
  });
  
  class MM {
    constructor() {
      this.frames = new Stack();
      this.labels = {};
    }

    read(block) {
      this.frames.push();
      for (const stmt of block) {
        const [first, second] = stmt;
        if (first == "$c") {
          const [, vars] = stmt;
          for (const varz of vars) {
            this.frames.addC(varz);
          }
        } else if (first == "$v") {
          const [, vars] = stmt;
          for (const varz of vars) {
            this.frames.addV(varz);
          }
        } else if (first == "${") {
          const [p, inner, q] = stmt;
          this.read(inner);
        } else if (second == "$f") {
          const [label, f, type, variable] = stmt;
          this.frames.addF(variable, type, label);
          this.labels[label] = [f, [type, variable]];
        } else if (second == "$d") {
          throw new Error(`Unsupported statement type $d.`);
        } else if (second == "$a") {
          const [label, a, type, rule] = stmt;
          const axiom = this.frames.assert(type, rule);
          ///if (label == "ax-mp") {
          // console.log(stmt);
          //console.log(axiom);          
          //throw new Error("hi");
          //}
          this.labels[label] = [a, axiom];
        } else if (second == "$e") {
          const [label, e, type, rule] = stmt;
          this.frames.addE(rule, type, label);
          this.labels[label] = [e, [type, rule]];
        } else if (second == "$p") {
          const [label, p, type, theorem, d, proof] = stmt;
          this.verify(label, type, theorem, proof);
          this.labels[label] = [p, this.frames.assert(type, theorem)];
        } else {
          throw new Error(`Unknown statement type`);
        }
      }
      
      return this.frames.pop();
    }

    decompress(type, theorem, proof) {
      const [d, f, e] = this.frames.assert(type, theorem);

      const labels = [];

      const args = f
            .map(([k, v]) => v)
            .map((v) => this.frames.lookupF(v));
     
      const hyps = e
            .map(([rule, type]) => this.frames.lookupE(rule, type));
      labels.push(...args);
      labels.push(...hyps);

      const m = labels.length;

      const [l, local, r, compressed] = proof;

      const n = local.length;

      let integers = [];
      let current = 0;

      for (let ch of compressed) {
        if (ch >= 'A' && ch <= 'T') {
          // Shift the current integer left by 20 bits.
          let result = current * 20;
          // Add the next 20 bits as the least significant bits.
          result += ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
          integers.push(result);
          // Reset the current integer.
          current = 0;
          // throw new Error(ch);
        } else if (ch >= 'U' && ch < 'Y') {
          // Shift the current integer left by 5 bits.
          current = current * 5;
          // Add the next 5 bits as the last significant bits.
          current += ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
        } else if (ch == 'Z') {
          throw new Error("marker");
        } else {
          throw new Error(`Unexpected character "${ch}" in compressed proof`);
        }
      }

      const result = [];
      for (const integer of integers) {
        if (integer > 0 && integer <= m) {
          result.push(labels[integer - 1]);
        } else if (integer > m && integer <= (m + n)) {
          const i = integer - m;
          result.push(local[i - 1]);
        } else {
          throw new Error(`Invalid integer number "${integer}" in compressed proof.`);
        }
      }

      return result;
    }
    
    verify(label, type, theorem, proof) {
      if (proof[0] == "(") {
        proof = this.decompress(type, theorem, proof);
      }

      // console.log(proof);
      
      const stack = [];
      for (const step of proof) {
        const [op, data] = this.labels[step];
        if (op == "$e" || op == "$f") {
          const [type, varz] = data;
          //console.log(`push ${op} ${step}: ${data.flat().join(" ")}`);
          //console.log(data);
          //throw new Error("hi");
          stack.push([type, [varz]]);
        } else if (op == "$a" || op == "$p") {
          const [dist, mandatory, hyp, result] = data;
          const subs = {};
          //console.log(`call ${op} ${step}: ${mandatory.length} args and ${hyp.length} logical`);
          //console.log(`Stack:`);
          //for (let entry of [...stack].reverse()) {
          //  console.log(`- [${entry.flat().join(" ")}]`);
          //}

          const npop = mandatory.length + hyp.length;
          const base = stack.length - npop;
          let sp = base;
          //console.log(`base (${base}) = top (${stack.length}) - (${npop})`);
          //console.log(stack[sp]);
          
          for (const [k, v] of mandatory) {
            const top = stack[sp];
            // console.log(`- poping [${top.flat().join(" ")}]`);
            if (top[0] != k) {
              throw new Error(`Argument types don't match. Expected ${k} but got ${top[0]}.`);
            }
            subs[v] = top[1];
            sp++;
          }

          // console.log(hyp);

          // TODO: go through the logical hypothesis.
          //console.log(subs);
          //console.log(hyp);
          for (const [h, type] of hyp) {
            const top = stack[sp];
            //console.log(`- poping [${top.flat().join(" ")}]`);
            if (top[0] != type) {
              throw new Error(`Argument types don't match. Expected ${type} but got ${top[0]}.`);
            }
            
            const sub = h
                  .map((tok) => subs[tok] ? subs[tok] : tok);
            // console.log(top[1]);
            if (top[1].flat().join("") != sub.flat().join("")) {
              //console.log(top[1]);
              //console.log(sub);
              throw new Error(`Argument values don't match. Expected ${sub} but got ${top[1]}.`);
            }
            sp++;
            // throw new Error("Need to go through the logical hypothesis");
          }

          stack.splice(base, npop);
          // console.log(sp);

          const el = result[1]
                .map((tok) => subs[tok] ? subs[tok] : tok);

          // console.log(el);
          //console.log(`... and pushing ${result[0]} ${el.flat().join(" ")}`);
          
          stack.push([result[0], el.flat()]);

          //console.log(`Stack:`);
          //for (let entry of [...stack].reverse()) {
          //  console.log(`- [${entry.flat().join(" ")}]`);
          //}

          // throw new Error("hi");


        }
      }

      if (stack.length != 1) {
        throw new Error(`Stack has more than one entry left`);
      }

      const [, last] = stack.pop();
      if (last.join("") != theorem.join("")) {
        throw new Error(`Assertion proved doesn't match: ${last.join("")} != ${theorem.join("")}`);
      }
    }
  }

  it("wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.", () => {
    const mm = new MM();
    const top = mm.read(parse(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `, true));
    
    assertThat(mm.labels["w2"])
      .equalsTo(["$a", [
        [],
        [["wff", "p"], ["wff", "q"]],
        [],
        ["wff", ["(", "p", "->", "q", ")"]]
      ]]);
    
    assertThat(top.v)
      .equalsTo(new Set(["p", "q", "r", "s"]));

  });

  it.skip("decompress", () => {
    const proof = [ '(', [ 'wi', 'ax-mp' ], ')', 'BCEABCGDFHH' ];
    
  });
  
  it.skip("modus ponens", () => {
    const [code] = parse(`
      $c ( ) -> wff ~ $.
      $v p q r $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      wi $a wff ( p -> q ) $.
      wn $a wff ~ p $.

      ax-1 $a wff ( p -> ( q -> p ) ) $.
      ax-2 $a wff ( ( p -> ( q -> r ) ) -> ( ( p -> q ) -> ( p -> r ) ) ) $.
      ax-3 $a wff ( ( ~ p -> ~ q ) -> ( q -> p ) ) $.

      $\{
        min $e wff ph $.
        maj $e wff ( ph -> ps ) $.
        ax-mp $a wff ps $.
      $\}

      $\{
        mp2.1 $e |- ph $.
        mp2.2 $e |- ps $.
        mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
        $( A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.) $)
        mp2 $p |- ch $= ( wi ax-mp ) BCEABCGDFHH $.
      $\}

    `);

    const mm = new MM().read(code);
  });

  it("Propositional Calculus", () => {
      const [code] = parse(`
        $( Declare the primitive constant symbols for propositional calculus. $)
        $c ( $.  $( Left parenthesis $)
        $c ) $.  $( Right parenthesis $)
        $c -> $. $( Right arrow (read:  "implies") $)
        $c -. $. $( Right handle (read:  "not") $)
        $c wff $. $( Well-formed formula symbol (read:  "the following symbol
                     sequence is a wff") $)
        $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
                    'a proof exists for") $)
      
        $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
        $( Introduce some variable names we will use to represent well-formed
           formulas (wff's). $)
        $v ph $.  $( Greek phi $)
        $v ps $.  $( Greek psi $)
        $v ch $.  $( Greek chi $)
        $v th $.  $( Greek theta $)
        $v ta $.  $( Greek tau $)
        $v et $.  $( Greek eta $)
        $v ze $.  $( Greek zeta $)
        $v si $.  $( Greek sigma $)
        $v rh $.  $( Greek rho $)
        $v mu $.  $( Greek mu $)
        $v la $.  $( Greek lambda $)
        $v ka $.  $( Greek kappa $)
      
        $( Specify some variables that we will use to represent wff's.
           The fact that a variable represents a wff is relevant only to a theorem
           referring to that variable, so we may use $f hypotheses.  The symbol
           "wff" specifies that the variable that follows it represents a wff. $)
        $( Let variable "ph" be a wff. $)
        wph $f wff ph $.
        $( Let variable "ps" be a wff. $)
        wps $f wff ps $.
        $( Let variable "ch" be a wff. $)
        wch $f wff ch $.
        $( Let variable "th" be a wff. $)
        wth $f wff th $.
        $( Let variable "ta" be a wff. $)
        wta $f wff ta $.
        $( Let variable "et" be a wff. $)
        wet $f wff et $.
        $( Let variable "ze" be a wff. $)
        wze $f wff ze $.
        $( Let variable "si" be a wff. $)
        wsi $f wff si $.
        $( Let variable "rh" be a wff. $)
        wrh $f wff rh $.
        $( Let variable "mu" be a wff. $)
        wmu $f wff mu $.
        $( Let variable "la" be a wff. $)
        wla $f wff la $.
        $( Let variable "ka" be a wff. $)
        wka $f wff ka $.


        $(
        #*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        The Syntax Propositional calculus
        #*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        $)

        wn $a wff -. ph $.

        wi $a wff ( ph -> ps ) $.

        $(
        =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The Axioms of Propositional Calculus
        =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        $)

        $\{
          $( Minor premise for modus ponens. $)
          min $e |- ph $.
          $( Major premise for modus ponens. $)
          maj $e |- ( ph -> ps ) $.
          $( Rule of Modus Ponens.  The postulated inference rule of propositional
             calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  The rule says, "if
             'ph' is true, and 'ph' implies 'ps' , then 'ps' must also be
             true."  This rule is sometimes called "detachment," since it detaches
             the minor premise from the major premise.  "Modus ponens" is short for
             "modus ponendo ponens," a Latin phrase that means "the mode that by
             affirming affirms" - remark in [Sanford] p. 39.  This rule is similar to
             the rule of modus tollens ~ mto .

             Note:  In some web page displays such as the Statement List, the
             symbols " '&' " and " '=>' " informally indicate the relationship
             between the hypotheses and the assertion (conclusion), abbreviating the
             English words "and" and "implies."  They are not part of the formal
             language.  (Contributed by NM, 30-Sep-1992.) $)
          ax-mp $a |- ps $.
       $\}

       $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
          propositional calculus.  The 3 axioms are also given as Definition 2.1 of
          [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
          simplification" in _Principia Mathematica_ (Theorem *2.02 of
          [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
          assertion of 'ph' and 'ps' to the assertion of 'ph' simply."  It is
          Proposition 1 of [Frege1879] p. 26, its first axiom.  (Contributed by NM,
          30-Sep-1992.) $)
        ax-1 $a |- ( ph -> ( ps -> ph ) ) $.


        $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
           propositional calculus.  It "distributes" an antecedent over two
           consequents.  This axiom was part of Frege's original system and is known
           as _Frege_ in the literature; see Proposition 2 of [Frege1879] p. 26.  It
           is also proved as Theorem *2.77 of [WhiteheadRussell] p. 108.  The other
           direction of this axiom also turns out to be true, as demonstrated by
           ~ pm5.41 .  (Contributed by NM, 30-Sep-1992.) $)
        ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.


        $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
           propositional calculus.  It swaps or "transposes" the order of the
           consequents when negation is removed.  An informal example is that the
           statement "if there are no clouds in the sky, it is not raining" implies
           the statement "if it is raining, there are clouds in the sky."  This axiom
           is called _Transp_ or "the principle of transposition" in _Principia
           Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).  We will also
           use the term "contraposition" for this principle, although the reader is
           advised that in the field of philosophical logic, "contraposition" has a
           different technical meaning.  (Contributed by NM, 30-Sep-1992.)  Use its
           alias ~ con4 instead.  (New usage is discouraged.) $)
        ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

        $(
        =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication
        =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        $)

        $\{
          mp2.1 $e |- ph $.
          mp2.2 $e |- ps $.
          mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
          $( A double modus ponens inference.  (Contributed by NM, 5-Apr-1994.) $)
          mp2 $p |- ch $=
            ( wi ax-mp ) BCEABCGDFHH $.
        $\}

        $\{
          mp2b.1 $e |- ph $.
          mp2b.2 $e |- ( ph -> ps ) $.
          mp2b.3 $e |- ( ps -> ch ) $.
          $( A double modus ponens inference.  (Contributed by Mario Carneiro,
             24-Jan-2013.) $)
          mp2b $p |- ch $=
            ( ax-mp ) BCABDEGFG $.
        $\}

        $\{
          a1i.1 $e |- ph $.
          $( Inference introducing an antecedent.  Inference associated with ~ ax-1 .
             Its associated inference is ~ a1ii .  See ~ conventions for a definition
             of "associated inference".  (Contributed by NM, 29-Dec-1992.) $)
          a1i $p |- ( ps -> ph ) $=
            ( wi ax-1 ax-mp ) ABADCABEF $.
        $\}


        $\{
          2a1i.1 $e |- ph $.
          $( Inference introducing two antecedents.  Two applications of ~ a1i .
             Inference associated with ~ 2a1 .  (Contributed by Jeff Hankins,
             4-Aug-2009.) $)
          2a1i $p |- ( ps -> ( ch -> ph ) ) $=
           ( wi a1i ) CAEBACDFF $.
        $\}

        $\{
          mp1i.1 $e |- ph $.
          mp1i.2 $e |- ( ph -> ps ) $.
          $( Inference detaching an antecedent and introducing a new one.
             (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
          mp1i $p |- ( ch -> ps ) $=
            ( ax-mp a1i ) BCABDEFG $.
        $\}

    `);

    const mm = new MM().read(code);
  });


  
});


function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
