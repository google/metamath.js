const Assert = require("assert");

const {parse} = require("../src/parser.js");
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

    const mm = new MM();
    mm.read(code);

    //console.log(mm.labels["mp2"][2]);
    
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

    `);

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
  
  it("Hofstadter's PQ", () => {
    const [code] = parse(`
      $c wff |- p q - $.
      $v x y z $.
      wx $f wff x $.
      wy $f wff y $.
      wz $f wff z $.

      $( 1 is a wff $)
      w0 $a wff - $.          

      $( n is a wff $)
      w1 $a wff x - $.

      $( 2 is a wff $)
      t0 $p wff - - $= w0 w1 $.

      $( 3 is a wff $)
      t1 $p wff - - - $= w0 w1 w1 $.

      $( x + - = x - $)
      ax0 $a |- x p - q x - $.

      $( 1 + 1 = 2 $)
      t2 $p |- - p - q - - $= w0 ax0 $.

      $( 2 + 1 = 3 $)
      t3 $p |- - - p - q - - - $= w0 w1 ax0 $.

      $( 3 + 1 = 4 $)
      t4 $p |- - - - p - q - - - - $= w0 w1 w1 ax0 $.

      $( if x + y = z then x + y + 1 = z + 1 $)
      $\{
        ax1.1 $e |- x p y q z $.
        ax1 $a |- x p y - q z - $.
      $\}

      $( 1 + 2 = 3 $)
      t5 $p |- - p - - q - - - $= 
        w0             $( x = -, i.e. 1 $)
        w0             $( y = -, i.e. 1 $)
        w0 w1          $( z = - -, i.e. 2 $)
        w0 ax0         $( |- - p - q - -, i.e. 1 + 1 = 2 $)
        ax1            $( |- - p - - q - - - , i.e. 1 + 2 = 3 $)
        $.

      $( 1 + 3 = 4 $)
      t6 $p |- - p - - - q - - - - $= 
        w0             $( x = -, i.e. 1 $)
        w0 w1          $( y = - -, i.e. 2 $)
        w0 w1 w1       $( z = - - -, i.e. 3 $)
        t5             $( |- - p - - q - - -, i.e. 1 + 2 = 3 $)
        ax1            $( |- - p - - - q - - - -, i.e. 1 + 3 = 4 $)
        $.
    `);

    const mm = new MM();
    mm.read(code);
  });

  it("Hofstadter's TQ", () => {
    const [code] = parse(`
      $c wff |- p q - $.
      $v x y z $.
      wx $f wff x $.
      wy $f wff y $.
      wz $f wff z $.

      $( 1 is a wff $)
      w0 $a wff - $.          

      $( n is a wff $)
      w1 $a wff x - $.

      $( 2 is a wff $)
      t0 $p wff - - $= w0 w1 $.

      $( 3 is a wff $)
      t1 $p wff - - - $= w0 w1 w1 $.

      $( x * 1 = x $)
      ax0 $a |- x t - q x $.

      $( 1 * 1 = 1 $)
      t2 $p |- - t - q - $= w0 ax0 $.

      $( 2 * 1 = 2 $)
      t3 $p |- - - t - q - - $= t0 ax0 $.

      $( if x * y = z then x * (y + 1) = (z + x) $)
      $\{
        ax1.1 $e |- x t y q z $.
        ax1 $a |- x t y - q z x $.
      $\}

      $( since 1 * 1 = 1 then 1 * 2 = 2 $)
      t4 $p |- - t - - q - - $= 
        w0             $( x = -, i.e. 1 $)
        w0             $( y = -, i.e. 1 $)
        w0             $( z = -, i.e. 1 $)
        w0 ax0         $( |- - t - q - -, i.e. 1 * 1 = 1 $)
        ax1            $( |- - t - - q - - , i.e. 1 * 2 = 2 $)
      $.

      $( since 2 * 1 = 2 then 2 * 2 = 4 $)

      $( since 2 * 2 = 4 then 2 * 3 = 6 $)
      t6 $p |- - t - - q - - $= 
        w0             $( x = -, i.e. 1 $)
        w0             $( y = -, i.e. 1 $)
        w0             $( z = -, i.e. 1 $)
        w0 ax0         $( |- - t - q - -, i.e. 1 * 1 = 1 $)
        ax1            $( |- - t - - q - - , i.e. 1 * 2 = 2 $)
      $.
    `);

    const mm = new MM();
    mm.read(code);
  });

  
});


function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
