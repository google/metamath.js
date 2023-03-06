const Assert = require("assert");
const moo = require("moo");

const {parse, grammar, lexicon} = require("../src/parser.js");
const {Frame, Stack, MM} = require("../src/metamath.js");

describe("Verifier", () => { 
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
        .equalsTo(`Undeclared type of "bar".`);
    }

    stack.addV("bar");
    stack.addF("bar", "a", "bar");

    stack.addE(["bar"], "|-", "foo");
    assertThat(stack.lookupE([["bar"], "|-"])).equalsTo("foo");

    try {
      stack.lookupE("hello");
      throw new Error("Expected to fail before.");
    } catch (e) {
      assertThat(e.message)
        .equalsTo(`Undeclared logical requirement "hello".`);
    }

    assertThat(stack.assert("foo", ["bar"]))
      .equalsTo([
        [],
        [["a", "bar", "bar"]],
        [[["bar"], "|-", "foo"]],
        ["foo", ["bar"]]
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
    assertThat(new MM().read(...parse(`
      $c a $.
    `)).c)
      .equalsTo(new Set(["a"]));
  });

  it("$v b $.", () => {
    assertThat(new MM().read(...parse(`
      $v b $.
    `)).v)
      .equalsTo(new Set(["b"]));
  });
  
  it("$c a $. $v b $.", () => {
    assertThat(new MM().read(...parse(`
        $c a $.
        $v b $.
    `)).c)
      .equalsTo(new Set(["a"]));
  });
  
  it("$c a $. $v b $.", () => {
    assertThat(new MM().read(...parse(`
        $c a $.
        $v b $.
    `)).v)
      .equalsTo(new Set(["b"]));
  });
  
  it("${ $v a b c $. $}", () => {
    assertThat(new MM().read(...parse(`
      $\{
        $v a b c $.
      $\}
    `)).v)
      .equalsTo(new Set([]));
    // The top frame has no variables.
  });
  
  it("$d a b $.", () => {
    try {
      new MM().read(...parse(`
        $( This should fail because a needs to be declared $)
        $d a b $.
      `));
      throw new Error("Not supposed to reach this");
    } catch (e) {
      assertThat(e.message)
        .equalsTo("Disjoint statement of undeclared variable a.");
      return;
    }
    throw new Error("Expected exception to be thrown.");
  });
  
  it("$v a $. $d a $.", () => {
    try {
      new MM().read(...parse(`
        $( This should fail because you need at least two variables to be disjoint $)
        $v a $.
        $d a $.
      `));
      throw new Error("Not supposed to reach this");
    } catch (e) {
      assertThat(e.message)
        .equalsTo("Invalid disjoint statement: need at least two variables.");
      return;
    }
    throw new Error("Expected exception to be thrown.");
  });
  
  it("$v a b $. $d a b $.", () => {
    assertThat(new MM().read(...parse(`
        $v a b $.
        $d a b $.
      `)).d).equalsTo(new Set([["a", "b"]]));
  });

  it("$v a b $. $d a b $. $d a b $.", () => {
    assertThat(new MM().read(...parse(`
        $v a b $.
        $d a b $.
        $( duplicate statement $)
        $d a b $.
      `)).d).equalsTo(new Set([["a", "b"]]));
  });

  it("$v w x y z $. $d w x y z $.", () => {
    assertThat(new MM().read(...parse(`
        $v w x y z $.
        $d w x y z $.
      `)).d).equalsTo(new Set([["w", "x"], ["w", "y"], ["w", "z"], ["x", "y"], ["x", "z"], ["y", "z"]]));
  });
  
  it("$v x y A B $. $d x y A $. $d x y B $.", () => {
    assertThat(new MM().read(...parse(`
        $v x y A B $.
        $d x y A $.
        $d x y B $.
      `)).d).equalsTo(new Set([["x", "y"], ["A", "x"], ["A", "y"], ["B", "x"], ["B", "y"]]));
  });
  
  it("w2 $a wff ( p -> q ) $.", () => {
    const mm = new MM();
    mm.read(...parse(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
    `));
    assertThat(mm.labels["w2"])
      .equalsTo(["$a", [
        [],
        [["wff", "p", "wp"], ["wff", "q", "wq"]],
        [],
        ["wff", ["(", "p", "->", "q", ")"]]
      ]]);
  }); 

  it("w2 $a wff ( p -> q ) $.", () => {
    const mm = new MM();
    mm.read(...parse(`
      $c ( ) -> wff $.
      $v p q $.
      wp $f wff p $.
      wq $f wff q $.
      $d p q $.
      w2 $a wff ( p -> q ) $.
    `));
    assertThat(mm.labels["w2"])
      .equalsTo(["$a", [
        [["p", "q"]], // disjoint variables conditions
        [["wff", "p", "wp"], ["wff", "q", "wq"]], // type hypothesis
        [], // logical hypothesis
        ["wff", ["(", "p", "->", "q", ")"]]
      ]]);
  }); 

  it("assert()", () => {
    const stack = new Stack();
    stack.push();
    stack.addC("A");
    stack.addC("~");
    stack.addC("->");
    assertThat(stack.top().c).equalsTo(new Set(["A", "~", "->"]));
    stack.addV("a");
    stack.addV("b");
    stack.addV("c");
    assertThat(stack.top().v).equalsTo(new Set(["a", "b", "c"]));
    assertThat(stack.lookupV("a"));
    // Variable a is of type A.
    stack.addF("a", "A", "let1");
    stack.addF("b", "A", "let3");
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
      ["A", "a", "let1"],
      ["A", "b", "let3"],
      ["A", "c", "let2"],
    ]);
    assertThat(hyps).equalsTo([[["~", "a"], "|-", "hypothesis"]]);
    stack.pop();

    stack.pop();
  });
  
  it("wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.", () => {
    const mm = new MM();
    const top = mm.read(...parse(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `));
    
    assertThat(mm.labels["w2"])
      .equalsTo(["$a", [
        [],
        [["wff", "p", "wp"], ["wff", "q", "wq"]],
        [],
        ["wff", ["(", "p", "->", "q", ")"]]
      ]]);
    
    assertThat(top.v)
      .equalsTo(new Set(["p", "q", "r", "s"]));

  });

  it.skip("decompress", () => {
    const proof = [ '(', [ 'wi', 'ax-mp' ], ')', 'BCEABCGDFHH' ];
    
  });
  
  it("modus ponens", () => {
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
        min $e |- p $.
        maj $e |- ( p -> q ) $.
        ax-mp $a |- q $.
      $\}

      $\{
        mp2.1 $e |- p $.
        mp2.2 $e |- q $.
        mp2.3 $e |- ( p -> ( q -> r ) ) $.
        mp2 $p |- r $= wq wr mp2.2 wp wq wr wi mp2.1 mp2.3 ax-mp ax-mp $.
      $\}

    `);

    const mm = new MM("mp2");
    mm.read(code);

    assertThat(mm.labels["$c"]).equalsTo([
      ["$c", ["(", ")", "->", "wff", "~"], "$."]
    ]);

    assertThat(mm.labels["$v"]).equalsTo([
      ["$v", ["p", "q", "r"], "$."]
    ]);

    assertThat(mm.labels["mp2"][1][2]).equalsTo([
      [["p"], "|-", "mp2.1"],
      [["q"], "|-", "mp2.2"],
      [["(", "p", "->", "(", "q", "->", "r", ")", ")"], "|-", "mp2.3"],
    ]);

    assertThat(mm.labels["mp2"][2]()).equalsTo([
      ["wq", ["wff", ["q"]], []],
      ["wr", ["wff", ["r"]], []],
      ["mp2.2", ["|-", [["q"]]], []],
      ["wp", ["wff", ["p"]], []],
      ["wq", ["wff", ["q"]], []],
      ["wr", ["wff", ["r"]], []],
      ["wi", ["wff", ["(", "q", "->", "r", ")"]], [4, 5]], // 5, 4
      ["mp2.1", ["|-", [["p"]]], []],
      ["mp2.3", ["|-", [["(", "p", "->", "(", "q", "->", "r", ")", ")"]]], []],
      ["ax-mp", ["|-", ["(", "q", "->", "r", ")"]], [3, 6, 7, 8]], // 8, 7, 6, 3
      ["ax-mp", ["|-", ["r"]], [0, 1, 2, 9]], // 9, 2, 1, 0
    ]);
    
  });

  it("Propositional Calculus", () => {
    const source = `
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

       $( Alias for ~ ax-3 to be used instead of it for labeling consistency.  Its
          associated inference is ~ con4i and its associated deduction is ~ con4d .
          (Contributed by BJ, 24-Dec-2020.) $)
       con4 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
           ( ax-3 ) ABC $.

       $\{
          con4i.1 $e |- ( -. ph -> -. ps ) $.
        $( Inference associated with ~ con4 .  Its associated inference is ~ mt4 .

           Remark: this can also be proved using ~ notnot followed by ~ nsyl2 ,
           giving a shorter proof but depending on more axioms (namely, ~ ax-1 and
           ~ ax-2 ).  (Contributed by NM, 29-Dec-1992.) $)
        con4i $p |- ( ps -> ph ) $=
          ( wn wi con4 ax-mp ) ADBDEBAECABFG $.
       $\}

       $\{
          mt4.1 $e |- ph $.
          mt4.2 $e |- ( -. ps -> -. ph ) $.
          $( The rule of modus tollens.  Inference associated with ~ con4i .
             (Contributed by Wolf Lammen, 12-May-2013.) $)
          mt4 $p |- ps $=
            ( con4i ax-mp ) ABCBADEF $.
       $\}

       $\{
          pm2.21i.1 $e |- -. ph $.
          $( A contradiction implies anything.  Inference associated with ~ pm2.21 .
             Its associated inference is ~ pm2.24ii .  (Contributed by NM,
             16-Sep-1993.) $)
          pm2.21i $p |- ( ph -> ps ) $=
            ( wn a1i con4i ) BAADBDCEF $.
       $\}

       $\{
          pm2.24ii.1 $e |- ph $.
          pm2.24ii.2 $e |- -. ph $.
          $( A contradiction implies anything.  Inference associated with ~ pm2.21i
             and ~ pm2.24i .  (Contributed by NM, 27-Feb-2008.) $)
          pm2.24ii $p |- ps $=
            ( pm2.21i ax-mp ) ABCABDEF $.
       $\}

    `;

    const [code] = parse(source);

    //for (let i = 0; i < 3000; i++) {
    //  const [code] = parse(source);
      //const foo = new MM();
      //foo.read(code);
    //}
    
    const mm = new MM();
    mm.read(code);

    // console.log(mm.labels["mp2"]);

    return;
    
    // console.log();
    const syntax = ["wff", "|-"];
    const name = "ax-mp";
    const [, [diff, args, conds, [t, rule]]] = mm.labels[name];
    // console.log(rule);
    const varz = args.map(([k, v]) => k + " " + v).join(", ");
    const such = conds.length == 0 ? "" : " | " + conds.map(([rule, type]) => type).join(", ");
    
    console.log(`axiom ${name}`);
    for (const [rule, type] of conds) {
      console.log(` if: ${type} ${rule.join(" ")}`);
    }
    
    console.log(` assert ${t} ${rule.join(" ")};`);
    //console.log(`${t} ${name}({${varz}${such}}) {`);
    //console.log(` return ${rule.join(" ")};`);
    //console.log(`}`);
    //console.log(JSON.stringify(a));

    
  });

  it("Hofstadter's MIU", () => {
    const source = require("fs").readFileSync("tests/miu.mm", {
      encoding: "utf8",
      flag: "r"
    });
    const [code] = parse(source);
    const mm = new MM();
    mm.read(code);
  });

  it("Hofstadter's MIU: Streaming", () => {
    const source = require("fs").readFileSync("tests/miu.mm", {
      encoding: "utf8",
      flag: "r"
    });
    const mm = new MM();
    mm.frames.push();
    const [code] = parse(source, mm);
    const frame = mm.frames.pop();
    assertThat(frame.c)
      .equalsTo(new Set(['M', 'I', 'U', '|-', 'wff']));
    assertThat(frame.v)
      .equalsTo(new Set(['x', 'y']));
    assertThat(frame.f)
      .equalsTo([[ 'x', 'wff' ], [ 'y', 'wff' ]]);
  });

  it("$c a $. $c b $.", () => {
    const mm = new MM();
    mm.frames.push();
    mm.feed(...parse(`
      $c a $.
    `));
    mm.feed(...parse(`
      $c b $.
    `));
    const frame = mm.frames.pop();
    assertThat(frame.c)
      .equalsTo(new Set(["a", "b"]));
  });
  
  it("Hofstadter's PQ", async () => {
    const fs = require("fs/promises");
    const nearley = require("nearley");
    const file = await fs.readFile("tests/pq.mm");

    const [code] = parse(file.toString());

    const mm = new MM();
    mm.read(code);
  });

  it("Hofstadter's TQ", async () => {
    const fs = require("fs/promises");
    const nearley = require("nearley");
    const file = await fs.readFile("tests/tq.mm");

    const [code] = parse(file.toString());

    const mm = new MM();
    mm.read(code);
  });
    
  it.skip("ax-5", () => {
    const [code] = parse(`
      $v x ph $.
      $\{
        $d x ph $.
        ax-5 $a |- ( ph -> A. x ph ) $.
      $\}
    `);

    const mm = new MM();
    mm.read(code);
  });
  
  it("id's proof", async () => {
    const file = await require("fs/promises").readFile("tests/id.mm");
    const [code] = parse(file.toString());
    const mm = new MM();
    mm.read(code);
  });

  it("idALT's proof", () => {
    const [code] = parse(`
      $c wff |- ( ) -> $.
      $v ph ps ch $.

      $( Let variable ph be a wff. $)
      wph $f wff ph $.

      $( Let variable ps be a wff. $)
      wps $f wff ps $.

      $( Let variable ch be a wff. $)
      wch $f wff ch $.

      wi $a wff ( ph -> ps ) $.

      ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
      ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

      $\{
        min $e |- ph $.
        maj $e |- ( ph -> ps ) $.
        ax-mp $a |- ps $.
      $\}

      $( [wph, wi, ax-1, ax-2, ax-mp] $)
      $( [wph, wph, wph, wi, *, wi, *, wph, wph, ax-1, wph, ...] $)
      idALT $p |- ( ph -> ph ) $=
        ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
    `);

    const mm = new MM();
    mm.read(code);

    const [p, [d, f, e]] = mm.labels["idALT"];
    // console.log(f);
    
    const [, , proof] = mm.labels["idALT"];
    assertThat(proof().map(([step]) => step)).equalsTo([
      'wph',  'wph',  'wph',  'wi',    'wi',
      'wph',  'wph',  'wi',   'wph',   'wph',
      'ax-1', 'wph',  'wph',  'wph',   'wi',
      'wph',  'wi',   'wi',   'wph',   'wph',
      'wph',  'wi',   'wi',   'wph',   'wph',
      'wi',   'wi',   'wph',  'wph',   'wph',
      'wi',   'ax-1', 'wph',  'wph',   'wph',
      'wi',   'wph',  'ax-2', 'ax-mp', 'ax-mp'
    ]);
  });

  it("decompress proof", () => {
    const [code] = parse(`
      $c wff |- ( ) -> $.
      $v ph ps ch $.

      $( Let variable ph be a wff. $)
      wph $f wff ph $.

      $( Let variable ps be a wff. $)
      wps $f wff ps $.

      $( Let variable ch be a wff. $)
      wch $f wff ch $.

      wi $a wff ( ph -> ps ) $.

      ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
      ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

      $\{
        min $e |- ph $.
        maj $e |- ( ph -> ps ) $.
        ax-mp $a |- ps $.
      $\}

      $( [wph, wi, ax-1, ax-2, ax-mp] $)
      $( [wph, wph, wph, wi, *, wi, *, wph, wph, ax-1, wph, ...] $)
      idALT $p |- ( ph -> ph ) $=
        ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
    `);

    const mm = new MM();
    mm.read(code);

    const compressed = "AAABZBZFAACAFABBGFBAFCAFADEE";
    
    assertThat(mm.numbers(compressed)).equalsTo([
      1,
      1,
      1,
      2,
      -1, // marker
      2,
      -1, // marker
      6,
      1,
      1,
      3,
      1,
      6,
      1,
      2,
      2,
      7,
      6,
      2,
      1,
      6,
      3,
      1,
      6,
      1,
      4,
      5,
      5
    ]);
    
    let result = mm.decompress(
      ["(", "wi ax-1 ax-2 ax-mp".split(" "), ")", compressed],
      ["wph"]);
    assertThat(result).equalsTo([
      'wph',  'wph',  'wph',  'wi',    'wi',
      'wph',  'wph',  'wi',   'wph',   'wph',
      'ax-1', 'wph',  'wph',  'wph',   'wi',
      'wph',  'wi',   'wi',   'wph',   'wph',
      'wph',  'wi',   'wi',   'wph',   'wph',
      'wi',   'wi',   'wph',  'wph',   'wph',
      'wi',   'ax-1', 'wph',  'wph',   'wph',
      'wi',   'wph',  'ax-2', 'ax-mp', 'ax-mp'
    ]);
  });

  it("peirceroll", () => {
    const [code] = parse(`
      $c wff |- ( ) -> $.
      $v ph ps ch th $.

      $( Let variable ph be a wff. $)
      wph $f wff ph $.

      $( Let variable ps be a wff. $)
      wps $f wff ps $.

      $( Let variable ch be a wff. $)
      wch $f wff ch $.

      $( Let variable th be a wff. $)
      wth $f wff th $.

      wi $a wff ( ph -> ps ) $.

      $( Makes imim1 an axiom to avoid proving it in this test $)
      imim1 $a |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $.

      $( Makes imim2 an axiom to avoid proving it in this test $)
      imim2 $a |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $.


      $( Makes sul5 an axiom to avoid proving it in this test $)
      $\{
        syl5.1 $e |- ( ph -> ps ) $.
        syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
        syl5 $a |- ( ch -> ( ph -> th ) ) $.
      $\}

      peirceroll $p |- ( ( ( ( ph -> ps ) -> ph ) -> ph )
                       -> ( ( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ph ) ) ) $=
        ( wi imim1 imim2 syl5 ) ABDZCDCADZHADZDJADIADHCAEJAIFG $.
    `);

    const mm = new MM();
    mm.read(code);
  });
  
  it.skip("Verify set.mm", async () => {
    const fs = require("fs/promises");
    const nearley = require("nearley");
    const file = await fs.readFile("tests/set.mm");
    const moo = require("moo");

    const mm = new MM();
    mm.frames.push();

    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(mm)));

    // TODO(goto): throws an exception at:
    //   - markers not supported in compressed proofs
    //   - $d statements not supported
    
    const code = file.toString();
    const lexer = moo.compile(lexicon);
    lexer.reset(code);
    do {
      const next = lexer.next();
      if (!next) {
        break;
      }
      //console.log(`Line: ${next.line}`);
      parser.feed(next.value);
    } while (true);

    const frame = mm.frames.pop();
    
  }).timeout(1000000);

  it("Verify demo0.mm", async () => {
    const fs = require("fs/promises");
    const nearley = require("nearley");
    const file = await fs.readFile("tests/demo0.mm");
    const moo = require("moo");
    const mm = new MM();
    mm.frames.push();
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(mm)));
    const code = file.toString();
    parser.feed(code);
    const frame = mm.frames.pop();
    [p, [dvs, args, , theorem], proof] = mm.labels["th1"];
    assertThat(args).equalsTo([["term", "t", "tt"]]);
    assertThat(theorem).equalsTo(["|-", ["t", "=", "t"]]);
    const summary = proof()
          .filter(([label, [type]]) => type == "|-")
          .map(
            ([label, [type, step]]) => `${label}: ${type} ${step.join(' ')}`
          );
    assertThat(summary)
      .equalsTo([
        "a2: |- ( t + 0 ) = t",
        "a2: |- ( t + 0 ) = t",
        "a1: |- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) )",
        "mp: |- ( ( t + 0 ) = t -> t = t )",
        "mp: |- t = t",
      ]);
  });

  it("Verify ql.mm", async () => {
    const fs = require("fs/promises");
    const nearley = require("nearley");
    const file = await fs.readFile("tests/ql.mm");
    const moo = require("moo");
    const mm = new MM();
    mm.frames.push();
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(mm)));
    const code = file.toString();
    parser.feed(code);
    const frame = mm.frames.pop();

    [p, [dvs, args, , theorem], proof] = mm.labels["id"];
    assertThat(args).equalsTo([["term", "a", "wva"]]);
    assertThat(theorem).equalsTo(["|-", ["a", "=", "a"]]);
    const summary = proof()
          .filter(([label, [type]]) => type == "|-")
          .map(
            ([label, [type, step]]) => `${label}: ${type} ${step.join(' ')}`
          );
    assertThat(summary)
      .equalsTo([
        "ax-a1: |- a = a ' '",
        "ax-a1: |- a = a ' '",
        "ax-r1: |- a ' ' = a",
        "ax-r2: |- a = a",
      ]);
  });

  it("trud", async () => {
    const file = await require("fs/promises").readFile("tests/trud.mm");
    const [code] = parse(file.toString());
    const mm = new MM();
    mm.read(code);
  });
    
  it("Verify hol.mm", async () => {
    const fs = require("fs/promises");
    const nearley = require("nearley");
    const file = await fs.readFile("tests/hol.mm");
    const moo = require("moo");
    const mm = new MM();
    mm.frames.push();
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(mm)));
    const code = file.toString();
    parser.feed(code);
    const frame = mm.frames.pop();

    [p, [dvs, args, , theorem], proof] = mm.labels["wal"];
    assertThat(args).equalsTo([["type", "al", "hal"]]);
    assertThat(theorem.flat().join(" ")).equalsTo("|- ! : ( ( al -> bool ) -> bool )");
    const summary = proof()
          .filter(([label, [type]]) => type == "|-")
          .map(
            ([label, [type, step]]) => `${label}: ${type} ${step.join(' ')}`
          );
    assertThat(summary)
      .equalsTo([
        "wv: |- p : ( al -> bool ) : ( al -> bool )",
        "wtru: |- T. : bool",
        "wl: |- \\ x : al . T. : ( al -> bool )",
        "weqi: |- [ p : ( al -> bool ) = \\ x : al . T. ] : bool",
        "wl: |- \\ p : ( al -> bool ) . [ p : ( al -> bool ) = \\ x : al . T. ] : ( ( al -> bool ) -> bool )",
        "df-al: |- T. |= [ ! = \\ p : ( al -> bool ) . [ p : ( al -> bool ) = \\ x : al . T. ] ]",
        "eqtypri: |- ! : ( ( al -> bool ) -> bool )",
      ]);
  });
});

describe("Verifier", () => {
  const {parse, process} = require("../src/descent.js");
  it("$c a b $.", () => {
    const c = [];
    parse(`$c a b $.`, {
      feed(e) {
        c.push(e);
      }
    });
    assertThat(c).equalsTo([["$c", ["a", "b"]]]);
  });

  it("$v a $.", () => {
    const v = [];
    parse(`$v a $.`, {
      feed(e) {
        v.push(e);
      }
    });
    assertThat(v).equalsTo([["$v", ["a"]]]);
  });

  it("$d a b $.", () => {
    const d = [];
    parse(`$d a b $.`, {
      feed(e) {
        d.push(e);
      }
    });
    assertThat(d).equalsTo([["$d", ["a", "b"]]]);
  });

  it("wp $f wff p $.", () => {
    const f = [];
    parse(`wp $f wff p $.`, {
      feed(e) {
        f.push(e);
      }
    });
    assertThat(f).equalsTo([["wp", "$f", "wff", "p"]]);
  });

  it("min $e wff ph $.", () => {
    const e = [];
    parse(`min $e wff ph $.`, {
      feed(statement) {
        e.push(statement);
      }
    });
    assertThat(e).equalsTo([["min", "$e", "wff", ["ph"]]]);
  });

  it("w2 $a wff ( p -> q ) $.", () => {
    const a = [];
    parse(`w2 $a wff ( p -> q ) $.`, {
      feed(statement) {
        a.push(statement);
      }
    });
    assertThat(a).equalsTo([["w2", "$a", "wff", ["(", "p", "->", "q", ")"]]]);
  });

  it("wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.", () => {
    const p = [];
    parse(`wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.`, {
      feed(statement) {
        p.push(statement);
      }
    });
    assertThat(p).equalsTo([[
      "wnew",
      "$p",
      "wff",
      ["(", "s", "->", "(", "r", "->", "p", ")", ")"],
      "$=",
      ["ws", "wr", "wp", "w2", "w2"]
    ]]);
  });

  it("a1i $p |- R |= A $= ( kt ax-trud syl ) BEABCFDG $.", () => {
    const p = [];
    parse(`a1i $p |- R |= A $= ( kt ax-trud syl ) BEABCFDG $.`, {
      feed(statement) {
        p.push(statement);
      }
    });
    assertThat(p).equalsTo([[
      "a1i",
      "$p",
      "|-",
      ["R", "|=", "A"],
      "$=",
      ["(", ["kt", "ax-trud", "syl"], ")", "BEABCFDG"]
    ]]);
  });

  it("${ $v a b c $. $}", () => {
    const frames = [];
    let v;
    parse("${ $v a b c $. $}", {
      feed(statement) {
        if (statement == "push") {
          frames.push([]);
        } else if (statement == "pop") {
          v = frames.pop();
        } else {
          frames[frames.length - 1].push(statement);
        }
      }
    });
    assertThat(v).equalsTo([["$v", ["a", "b", "c"]]]);
  });

  class StringReader {
    constructor(value) {
      this.value = value;
      this.i = 0;
    }
    async read() {
      if (this.i == this.value.length) {
        return {done: true};
      }
      let value = this.value[this.i];
      this.i++;
      return {done: false, value: value};
    }
  }

  it("StringReader", async () => {
    let reader = new StringReader("hello");
    assertThat(await reader.read()).equalsTo({done: false, value: 'h'});
    assertThat(await reader.read()).equalsTo({done: false, value: 'e'});
    assertThat(await reader.read()).equalsTo({done: false, value: 'l'});
    assertThat(await reader.read()).equalsTo({done: false, value: 'l'});
    assertThat(await reader.read()).equalsTo({done: false, value: 'o'});
    assertThat(await reader.read()).equalsTo({done: true});
  });
  
  it("wnew", async () => {
    const mm = process(`
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `);

    const [, proof] = mm.theorem("wnew");
    assertThat(proof().map(([step, [type, str]]) => `${step}: ${type} ${str.join(" ")}`)).equalsTo([
      'ws: wff s',
      'wr: wff r',
      'wp: wff p',
      'w2: wff ( r -> p )',
      'w2: wff ( s -> ( r -> p ) )'
    ]);
  });

  it("mp2", () => {
    const mm = process(`
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
        min $e |- p $.
        maj $e |- ( p -> q ) $.
        ax-mp $a |- q $.
      $\}

      $\{
        mp2.1 $e |- p $.
        mp2.2 $e |- q $.
        mp2.3 $e |- ( p -> ( q -> r ) ) $.
        mp2 $p |- r $= wq wr mp2.2 wp wq wr wi mp2.1 mp2.3 ax-mp ax-mp $.
      $\}
     `);

    const [, , proof] = mm.labels["mp2"];
    assertThat(proof() != undefined).equalsTo(true);
  });

  it("id", () => {
    const mm = process(`
      $c wff |- ( ) -> $.
      $v ph ps ch $.

      $( Let variable ph be a wff. $)
      wph $f wff ph $.

      $( Let variable ps be a wff. $)
      wps $f wff ps $.

      $( Let variable ch be a wff. $)
      wch $f wff ch $.

      wi $a wff ( ph -> ps ) $.

      ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

      $\{
        mpd.1 $e |- ( ph -> ps ) $.
        mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
        $(
          makes this an axiom as opposed to a theorem, so that we
          can skip bringing in the proof recursively.
          mpd $p |- ( ph -> ch ) $=
            ( wi a2i ax-mp ) ABFACFDABCEGH $.
        $)
        mpd $a |- ( ph -> ch ) $.
      $\}

      id $p |- ( ph -> ph ) $=
        ( wi ax-1 mpd ) AAABZAAACAECD $.

     `);

    const [, proof] = mm.theorem("id");
    assertThat(proof() != undefined).equalsTo(true);
  });

  it("miu.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/miu.mm");
    const mm = process(file.toString());
    assertThat(mm.theorems().map(([name, proof]) => proof()).length).equalsTo(1);
  });

  it("hol.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/hol.mm");
    const mm = process(file.toString());
    assertThat(mm.theorems().map(([name, proof]) => proof()).length).equalsTo(138);
  });

  it("ql.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/ql.mm");
    const mm = process(file.toString());
    assertThat(mm.theorems().map(([name, proof]) => proof()).length).equalsTo(1138);
  });

  it.skip("set.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/set.mm");
    const mm = process(file.toString());

    // console.log(mm.labels["$v"]);
    console.log(mm.labels["$c"].find(([c, [name]]) => name.includes('"')));
    // console.log(mm.labels["$c"].map(([c, [name]]) => name).join("\n"));
    return;
    
    const [, proof] = mm.theorem("young2d");
    assertThat(proof() != undefined).equalsTo(true);
    assertThat(mm.theorems().length).equalsTo(40142);

    return;

    // The following passes, but takes ~1 min, so we
    // only run it every now and then.
    
    for (let [name, proof] of mm.theorems()) {
      try {
        proof();
      } catch (e) {
        // TODO(goto): deal with array splicing limits.                                                                         
        if (e.message == "proof too long") {
          console.log(`Skipping ${name} because the proof is too long.`);
	      } else {
          throw e;
	      }
      }
    }    
  }).timeout(1000000);

  function build(program) {
    let root = [];
    let node = root;
    let parent = root;
    parse(program, {
      feed(statement) {
        if (statement == "push") {
          const block = [];
          node.push(block);
          parent = node;
          node = block;
        } else if (statement == "pop") {
          node = parent;
        } else {
          node.push(statement);
        }
      }
    });

    return root;
  }
  
  it("$v a $. $c b $. ${ $v c $. $}", async () => {
    const tree = build("$v a $. $c b $. ${ $v c $. $} $c d $.");
    assertThat(tree).equalsTo([
      ["$v", ["a"]],
      ["$c", ["b"]],
      [
        ["$v", ["c"]],
      ],
      ["$c", ["d"]],
    ]);
  });
});

describe("Scratch", () => {
  it.skip("Tarki's S2", () => {
    const source = require("fs").readFileSync("tests/tarski.mm", {
      encoding: "utf8",
      flag: "r"
    });
    const [code] = parse(source);
    const mm = new MM();
    mm.read(code);

    assertThat(mm.labels["wnotp"][2]() != undefined)
      .equalsTo(true);
    
    assertThat(mm.verifyAll())
      .equalsTo(6);
  });
});

function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
