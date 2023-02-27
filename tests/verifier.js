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
        [["a", "bar"]],
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
        [["wff", "p"], ["wff", "q"]],
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
        [["wff", "p"], ["wff", "q"]], // type hypothesis
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
      ["A", "a"],
      ["A", "b"],
      ["A", "c"],
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
  
  it("id's proof", () => {
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

      $( 1 1 1 2 Z 1 1 1 3 1 5 3 4 $)
      $( mandatory: wph $)
      $( local: wi ax-1 mpd $)
      $( decompressed: wph wph wph wi (Z) wph wph wph ax-1 wph (Z: wph wph wph wi) ax-1 mpd $)
      $(
       wph, wph, wph  wi                  wph, wph, wph         ax-1                          wph


                                          wff ph                                              wff ph
                                          wff ph                |- ( ph -> ( ph -> ph ) )     |- ( ph -> ( ph -> ph ) )
       wff ph                             wff ph                wff ph                        wff ph
       wff ph         wff ( ph -> ph )    wff ( ph -> ph )      wff ( ph -> ph )              wff ( ph -> ph )
       wff ph         wff ph              wff ph                wff ph                        wff ph


       wi                               ax-1                                        mpd

                        
       wff ( ph -> ph )                 
       wff ph                           |- ( ph -> ( ( ph -> ph ) -> ph ) )         
       |- ( ph -> ( ph -> ph ) )        |- ( ph -> ( ph -> ph ) )
       wff ph                           wff ph
       wff ( ph -> ph )                 wff ( ph -> ph )
       wff ph                           wff ph                                      |- ( ph -> ph )
      $)
      id $p |- ( ph -> ph ) $=
        ( wi ax-1 mpd ) AAABZAAACAECD $.
    `);

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
    assertThat(args).equalsTo([["term", "t"]]);
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
    assertThat(args).equalsTo([["term", "a"]]);
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

  it("trud", () => {
    const [code] = parse(`
      $( Declare the primitive constant symbols for lambda calculus. $)
      $c var $.   $( Typecode for variables (syntax) $)
      $c type $.  $( Typecode for types (syntax) $)
      $c term $.  $( Typecode for terms (syntax) $)
      $c |- $.    $( Typecode for theorems (logical) $)
      $c : $.     $( Typehood indicator $)
      $c . $.     $( Separator $)
      $c |= $.    $( Context separator $)
      $c bool $.     $( Boolean type $)
      $c ind $.   $( 'Individual' type $)
      $c -> $.    $( Function type $)
      $c ( $.     $( Open parenthesis $)
      $c ) $.     $( Close parenthesis $)
      $c , $.     $( Context comma $)
      $c \\ $.     $( Lambda expression $)
      $c = $.     $( Equality term $)
      $c T. $.    $( Truth term $)
      $c [ $.     $( Infix operator $)
      $c ] $.     $( Infix operator $)

      $v x y z f g p q $.  $( Bound variables $)
      $v A B C F R S T $.  $( Term variables $)

      $( Let variable A be a term. $)
      ta $f term A $.
      $( Let variable R be a term. $)
      tr $f term R $.
      $( Let variable S be a term. $)
      ts $f term S $.
      $( Let variable T be a term. $)
      tt $f term T $.

      $( Truth term. $)
      kt $a term T. $.

      $\{
        ax-syl.1 $e |- R |= S $.
        ax-syl.2 $e |- S |= T $.
        $( Syllogism inference. $)
        ax-syl $a |- R |= T $.

        $( Syllogism inference. $)
        syl $p |- R |= T $=
          ( ax-syl ) ABCDEF $.
          $( [8-Oct-2014] $)
      $\}

      $\{
        ax-trud.1 $e |- R : bool $.
        $( Deduction form of ~ tru . $)
        ax-trud $a |- R |= T. $.

        $( Deduction form of ~ tru . $)
        trud $p |- R |= T. $=
          ( ax-trud ) ABC $.
          $( [7-Oct-2014] $)

        ax-a1i.2 $e |- T. |= A $.

        $( Change an empty context into any context. $)
        a1i $p |- R |= A $=
          ( kt ax-trud syl ) BEABCFDG $.
          $( [7-Oct-2014] $)

      $\}
    `);
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
    assertThat(args).equalsTo([["type", "al"]]);
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

class Lexer {
  constructor() {
    const lexicon = {
      ["comment-expr"]: {match: /\/\*\*.*\*\//, lineBreaks: true},
      ["comment"]: {match: /\/\/.*\n/, lineBreaks: true},
      ["ws"]: {match: /[\s]+/, lineBreaks: true},
      ["theorem"]: "theorem",
      ["axiom"]: "axiom",
      ["proof"]: "proof",
      ["end"]: "end",
      ["let"]: "let",
      ["step"]: "step",
      ["const"]: "const",
      ["_include_"]: "include",
      ["assume"]: "assume",
      ["assert"]: "assert",
      ["("]: "(",
      [")"]: ")",
      ['"']: '"',
      [":"]: ":",
      [","]: ",",
      [";"]: ";",
      ["label"]: /[A-Za-z0-9-_.]+/,
      ["sequence"]: /[!-#%-~\?]+/,
    };
    this.lexer = moo.compile(lexicon);
  }
  parse(code) {
    this.lexer.reset(code);
  }
  next() {
    let next = this.lexer.next();
    if (!next) {
      this.head = undefined;
      return;
    }
    let {type, text} = next;
    this.head = [type, text];
    return this.head;
  }
  done() {
    assertThat(this.lexer.next()).equalsTo(undefined);
  }
  ws() {
    assertThat(this.next()[0]).equalsTo("ws");
  }
  eat(type, value) {
    assertThat(this.next()).equalsTo([type, value ? value : type]);
  };
}
  
class Parser {
  constructor() {
    this.lexer = new Lexer();
  }
  parse(code) {
    this.lexer.parse(code);
    return this.top();
  }
  eat(...types) {
    if (!this.lexer.head) {
      this.error();
    }
    for (let type of types) {
      if (this.lexer.head[0] == type) {
        const value = this.lexer.head[1];
        this.lexer.next();
        return value;
      }
    }
    this.error();
  }
  
  error() {
    const {head} = this.lexer;
    const {line, col} = this.lexer.lexer;
    throw new Error(`Unexpected token "${head[1]}" (${head[0]}) on line ${line} column ${col}.`);
  }
  
  accepts(...types) {
    if (!this.lexer.head) {
      return false;
    }
    for (let type of types) {
      if (this.lexer.head[0] == type) {
        return true;
      }
    }
    return false;
  }
  
  ws(optional = false) {
    const sp = ["ws", "comment", "comment-expr"];
    // const sp = ["ws"];
    if (this.accepts(...sp)) {
      this.eat(...sp);
      // allows multiple whitespace types intermingled
      while (this.accepts(...sp)) {
        this.eat(...sp);
      }
    } else if (!optional) {
      this.error();
    }
  }
  
  declaration(type, label = true, multiple = true) {
    const result = [];
    this.eat(type);
    this.ws();
    const symbol = [
      // a subset of possible symbols
      "label",
      // reserved keywords that can also be symbols
      '"',
      "(",
      ")",
      ",",
      ":",
      ";",
      "//",
      // catch all types of sequences
      "sequence",
    ];
    if (label) {
      result.push(this.eat(...symbol));
      this.ws(true);
      this.eat(":");
      this.ws(true);
    }
    let first = this.eat(...symbol);
    result.push(first);
    this.ws(false);
    let second = this.eat(...symbol);
    result.push(second);
    this.ws(false);
    if (multiple) {
      while (this.accepts(...symbol)) {
        result.push(this.eat(...symbol));
        this.ws(false);
      };
    }
    return [type, result];
  }

  axiom() {
    this.eat("axiom");
    this.ws();
    let name = this.eat("label");
    this.ws();
    let h = this.header();
    this.eat("end");
    this.ws();
    return ["axiom", name, h];
  }
  
  header() {
    this.ws(true);
    let lets = [];
    while (this.accepts("let")) {
      lets.push(this.declaration("let", true, false));
    }
    
    this.ws(true);
    let ifs = [];
    while (this.accepts("assume")) {
      ifs.push(this.declaration("assume", true, true));
    }
    
    this.ws(true);
    let then = this.declaration("assert", false, true);
    return [lets, ifs, then];
  }
  
  step() {
    const result = [];
    this.eat("step");
    this.eat("ws");
    result.push(this.eat("label"));
    this.ws(true);
    this.eat(")");
    this.ws(true);
    result.push(this.eat("label"));
    this.ws(true);
    this.eat("(");
    this.ws(true);
    let args = [];
    result.push(args);
    if (this.accepts("label")) {
      args.push(this.eat("label"));
      this.ws(true);
    }
    while (this.accepts(",")) {
      this.eat(",");
      this.ws(true);
      args.push(this.eat("label"));
    }
    this.ws(true);
    this.eat(")");
    this.ws(true);
    this.eat(":");
    this.ws(true);
    let sequence = [];
    result.push(sequence);
    while (this.accepts("label", "sequence")) {
      sequence.push(this.eat("label", "sequence"));
      this.ws(true);
    }
    return result;
  }
  
  theorem() {
    this.eat("theorem");
    this.ws();
    let name = this.eat("label");
    this.ws();
    let head = this.header();
    
    let steps = [];
    while (this.accepts("step")) {
      steps.push(this.step());
    }
    
    this.eat("end");
    this.ws();
    return ["theorem", name, head, steps];
  }
  
  include() {
    this.eat("_include_");
    this.ws();
    this.eat('"');
    const name = this.eat("label");
    this.eat('"');
    this.ws();
    return ["include", name];
  }
    
  top() {
    this.lexer.next();
    let result = [];
    do {
      if (this.accepts("ws")) {
        this.ws();
      } else if (this.accepts("//")) {
        throw new Error("hi");
      } else if (this.accepts("const")) {
        result.push(this.declaration("const", false));
      } else if (this.accepts("let")) {
        result.push(this.declaration("let"));
      } else if (this.accepts("axiom")) {
        result.push(this.axiom());
      } else if (this.accepts("theorem")) {
        result.push(this.theorem());
      } else if (this.accepts("_include_")) {
        result.push(this.include());
      } else {
        this.error();
      }
    } while (this.lexer.head);
    return result;
  }
}

describe("parser", () => {
  it("parser", () => {
    let result = new Parser().parse(`
      // hello world

      include "file.mm"

      // tokens
      const => + " ( ) ; : , & || |- /** this too is a comment */ // foo
      const M I U |- wff

      // variable declarations
      let wx: wff x
      let wy: wff y

      axiom mp
        let wp: wff p
        let wq: wff q

        // logical hypothesis
        assume maj: |- p => q
        assume min: |- p
        assert |- q
      end

      theorem foo
        assert |- ~ p
        step 1) foo(): p
        step 2) bar(1): ~ /** this is a comment */ p
      end
    `);
    
    assertThat(result).equalsTo([
      ["include", "file.mm"],
      ["const", ["=>", "+", '"', "(", ")", ";", ":", ",", "&", "||", "|-"]],
      ["const", ["M", "I", "U", "|-", "wff"]],
      ["let", ["wx", "wff", "x"]],
      ["let", ["wy", "wff", "y"]],
      ["axiom", "mp", [
        [
          ["let", ["wp", "wff", "p"]],
          ["let", ["wq", "wff", "q"]],
        ], [
          ["assume", ["maj", "|-", "p", "=>", "q"]],
          ["assume", ["min", "|-", "p"]],
        ], 
        ["assert", ["|-", "q"]],
      ]
      ],
      ["theorem", "foo", [
        [],
        [],
        ["assert", ["|-", "~", "p"]]
      ],
       [
         ["1", "foo", [], ["p"]],
         ["2", "bar", ["1"], ["~", "p"]],
       ]]
    ]);
  });
  
  it("lexer: const", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      const => + -
    `);
    lexer.ws("ws");
    lexer.eat("const");
    lexer.ws();
    lexer.eat("sequence", "=>");
    lexer.ws();
    lexer.eat("sequence", "+");
    lexer.ws();
    lexer.eat("label", "-");
    lexer.ws();
    lexer.done();
  });
  
  it("lexer: let", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      let wff x y
    `);
    lexer.ws();
    lexer.eat("let");
    lexer.ws();
    lexer.eat("label", "wff");
    lexer.ws();
    lexer.eat("label", "x");
    lexer.ws();
    lexer.eat("label", "y");
    lexer.ws();
    lexer.done();
  });
  
  it("lexer: theorem", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      theorem foobar
        let wff p
      proof
      end
    `);

    lexer.ws();
    lexer.eat("theorem");
    lexer.ws();
    lexer.eat("label", "foobar");
    lexer.ws();
    lexer.eat("let");
    lexer.ws();
    lexer.eat("label", "wff");
    lexer.ws();
    lexer.eat("label", "p");
    lexer.ws();
    lexer.eat("proof");
    lexer.ws();
    lexer.eat("end");
    lexer.ws();
    lexer.done();
  });
  
  it("lexer: axiom", async () => {
    let lexer = new Lexer();

    lexer.parse(`
      axiom foobar
        let wff p
        let wff q
        assume p => q
        assume |- p
        assert |- q
      end
    `);

    lexer.ws();
    assertThat(lexer.next()).equalsTo(["axiom", "axiom"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "foobar"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["let", "let"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "wff"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "p"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["let", "let"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "wff"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "q"]);
    // assertThat(next()).equalsTo([":", ":"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["assume", "assume"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "p"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["sequence", "=>"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "q"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["assume", "assume"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["sequence", "|-"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "p"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["assert", "assert"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["sequence", "|-"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "q"]);
    lexer.ws();
    //assertThat(next()).equalsTo(["proof", "proof"]);
    //assertThat(next()[0]).equalsTo("ws");
    // assertThat(next()).equalsTo([";", ";"]);
    // assertThat(next()[0]).equalsTo("ws");
    assertThat(lexer.next()).equalsTo(["end", "end"]);
    lexer.ws();
    // assertThat(done()).equalsTo(true);
    lexer.done();
  });
});

class Transpiler {
  split(program) {
    const result = {};

    const mm = new MM();
    mm.push();
    
    const {parse} = require("../src/descent.js");
    parse(program.toString(), {
      feed(statement) {
        if (statement == "push") {
          mm.push();
        } else if (statement == "pop") {
          mm.pop();
        } else {
          mm.feed([statement]);
        }
      }
    });

    let frame = mm.pop();
    const code =
`const ${[...frame.c].join(" ")}
var ${[...frame.v].join(" ")}
`;

    result["lexicon.mm"] = code;

    for (const [label, value] of Object.entries(mm.labels)) {
      const [stmt] = value;
      if (stmt == "$e" || stmt == "$f" || label == "$c" || label == "$v") {
        continue;
      // } else if (stmt == "$f") {
        // const [, [type, name]] = mm.labels[label];
        // const code = `let ${label}: ${type} ${name}`;
        // await fs.writeFile(`${dir}/${label}.mm`, code);
        // result[`${label}.mm`] = code;
      } else  if (stmt == "$a") {
        const [, [d, f, e, [type, axiom]]] = mm.labels[label];
        let args = f.map(([type, name]) => `  let ${type} ${name}`).join("\n");
        if (Object.entries(f).length  > 0) {
          args += "\n";
        }
        
        let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${type} ${seq.join(" ")}`).join("\n");

        if (Object.entries(e).length > 0) {
          assumptions += "\n";
        }

        const code =
`include "lexicon.mm"

axiom ${label}
${args}${assumptions}  assert ${type} ${axiom.join(' ')}
end
`;

        // await fs.writeFile(`${dir}/${label}.mm`, code);
        result[`${label}.mm`] = code;

      } else if (stmt == "$p") {
        const [, [d, f, e, [type, theorem]], func] = mm.labels[label];

        //let args = "(";
        let args = f.map(([type, name]) => `include "${name}.mm"`).join("\n");
        //args += ")";
        
        const proof = func();
        
        const steps = proof.map(([step]) => step);
        const header = [...new Set(steps)]
              .map((step) => `include "${step}.mm"\n`).join("");
          
        // const conds = e.length == 0 ? "" : " | " + e.map(([seq, type, label]) => `${label}: ${type} ${seq.join(" ")}`).join(", ");

        let conds = "";

        //if (e.length > 0) {
        //  args += " if (\n";
        //}
        
        let hypothesis = [];
        for (let [seq, type, label] of e) {
          hypothesis.push(`  assume ${label}: ${type} "${seq.join(" ")}"`);
        }
        
        //if (e.length >0 ) {
        //  args += hypothesis.join("\n");
        //  args += ")";
        //}
        
        let diff = [];
        if (d.length > 0) {
          args += " and (";
          // args += "  [";
        }
        for (let [x, y] of d) {
          diff.push(`${x} != ${y}`);
        }
        
        if (d.length > 0) {
          args += "" + diff.join(", ") + ")";
        }

        const body = proof.map(([step, [type, sequence], args], i) => `  step ${i}) ${step}(${args}): ${type} ${sequence.join(' ')}`).join("\n");
        
        const code =
`include "lexicon.mm"
${args}
${header}
theorem ${label}
  assert ${type} ${theorem.join(' ')}

${body}
end
`;
        
        // await fs.writeFile(`${dir}/${label}.mm`, code);
        result[`${label}.mm`] = code;
      } else {
        throw new Error(`Unknown statement type ${stmt}.`);
      }
    }
    return result;
  }
}

describe("transpiler", () => {
  const moo = require("moo");
  const fs = require("fs/promises");

  async function transpile(src) {
    const program = await fs.readFile(src);
    const files = await new Transpiler().split(program);

    const dir = `${src}.dir`;

    // Creates a directory if one doesn't exist
    try {
      const file = await fs.stat(dir);
      if (!file.isDirectory()) {
        throw new Error("hi");
      }
    } catch (e) {
      fs.mkdir(dir);
    }

    // console.log(files);

    for (let [name, content] of Object.entries(files)) {
      // console.log(name);
      await fs.writeFile(`${dir}/${name}`, content);
    }    
  }
    
  it("tq.mm", async () => {
    await transpile("tests/tq.mm");
  });

  it("pq.mm", async () => {
    await transpile("tests/pq.mm");
  });

  it("miu.mm", async () => {
    await transpile("tests/miu.mm");
  });

  it("demo0.mm", async () => {
    await transpile("tests/demo0.mm");
  });

  it("test.mm", async () => {
    await transpile("tests/test.mm");
  });
});

describe("Transpile and Parse", () => {
  it.skip("miu.mm", async () => {
    const fs = require("fs/promises");
    const src = "tests/miu.mm";
    const program = await fs.readFile(src);
    const files = await new Transpiler().split(program);
    // console.log(files);

    for (let [name, content] of Object.entries(files)) {
      // console.log(content);
      let parser = new Parser();
      try {
        parser.parse(content);
      } catch (e) {
        // console.log(e);
        console.log(name);
        console.log(content);
        throw e;
      }
    }
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
