/**
  *  Copyright 2022 Google LLC
  *
  *  Licensed under the Apache License, Version 2.0 (the "License");
  *  you may not use this file except in compliance with the License.
  *  You may obtain a copy of the License at
  *
  *      https://www.apache.org/licenses/LICENSE-2.0
  *
  *  Unless required by applicable law or agreed to in writing, software
  *  distributed under the License is distributed on an "AS IS" BASIS,
  *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  *  See the License for the specific language governing permissions and
  *  limitations under the License.
  **/

const Assert = require("assert");
const {parse, grammar} = require("../src/parser.js");
const {lexicon} = require("../src/lexer.js");
const moo = require("moo");
const nearley = require("nearley");

describe("Parser", () => { 
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

  it("$( a $)", () => {    
    assertThat(parse(`
      $(  first $)
      $c a $.
      $(  second $)
      $c b $.
    `))
      .equalsTo([[
        ["$c", ["a"], "$."],
        ["$c", ["b"], "$."],
      ]]);
  });

  it("$c a $.", () => {
    assertThat(parse(`
      $( hello $)
      $c a $.
    `)).equalsTo([[
      ["$c", ["a"], "$."]
    ]]);
  });

  it("$c ? $.", () => {
    assertThat(parse(`
      $( hello $)
      $c ? $.
    `)).equalsTo([[
      ["$c", ["?"], "$."]
    ]]);
  });

  it("$v a $.", () => {
    assertThat(parse(`
      $( hello $)
      $v a $.
    `)).equalsTo([[
      ["$v", ["a"], "$."]
    ]]);
  });

  it("$d a $.", () => {
    assertThat(parse(`
      $( hello $)
      $d a $.
    `)).equalsTo([[
      ["$d", ["a"], "$."]
    ]]);
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

  it("$v a $. $v b $. $v c $.", () => {    
    assertThat(parse("$v a $. $v b $. $v c $."))
      .equalsTo([[
        ["$v", ["a"], "$."],
        ["$v", ["b"], "$."],
        ["$v", ["c"], "$."]
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
    assertThat(parse("th1 $p |- t = t $= tt $( hi $) tze $."))
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
      $(  $)
      $(  $)
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

  it("$( a b $)", () => {    
    assertThat(parse(`
      $( a
         b
      $)
   `));
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

  it("$( comment $)", () => {
    for (let i = 0; i < 1; i++) {
      assertThat(parse("$( comment $)"))
        .equalsTo([
        ]);
    }
  });

  it("$(  $)", () => {
    assertThat(tokenize("$(  $)"))
      .equalsTo(["comment"]);
  });  

  it("$(  $)", () => {
    assertThat(tokenize(`
      $( a
         b $)
    `))
      .equalsTo(["ws", "comment", "ws"]);
  });

  it("$( comment $)", () => {
    assertThat(tokenize("$( comment $)"))
      .equalsTo([
        "comment"
      ]);
  });

  it("$( comment $)", () => {
    assertThat(tokenize(`
       $(
         comment
       $)
      `))
      .equalsTo([
        "ws",
        "comment",
        "ws"
      ]);
  });

  it("$( comment second $)", () => {
    assertThat(tokenize("$( comment second $)"))
      .equalsTo([
        "comment"
      ]);
  });

  it("$( 123 $)", () => {
    assertThat(tokenize("$( 123 $)"))
      .equalsTo([
        "comment"
      ]);
  });

  it.skip("$( $( $) $)", () => {
    // Nested comments are disallowed.
    assertThat(tokenize("$( $( $) $)"))
      .equalsTo([
        "comment"
      ]);
  });

  it("$( $f $)", () => {
    assertThat(tokenize("$( $f $)"))
      .equalsTo([
        "comment"
      ]);
  });

  it("$[ filename $]", () => {
    assertThat(tokenize("$[ filename $]"))
      .equalsTo([
        "lfile", "ws", "sequence", "ws", "rfile"
      ]);
  });

  it("$v a $.", () => {    
    assertThat(tokenize("$v a $."))
      .equalsTo(["v", "ws", "sequence", "ws", "dot"]);
  });

  it("$v a b $.", () => {    
    assertThat(tokenize("$v a b $."))
      .equalsTo(["v", "ws", "sequence", "ws", "sequence", "ws", "dot"]);
  });

  it("$( $v $)", () => {
    assertThat(tokenize("$( $v $)"))
      .equalsTo([
        "comment"
      ]);
  });

  it("$c a $.", () => {    
    assertThat(tokenize("$c a $."))
      .equalsTo(["c", "ws", "sequence", "ws", "dot"]);
  });

  it("$c = $.", () => {    
    assertThat(tokenize("$c = $."))
      .equalsTo(["c", "ws", "sequence", "ws", "dot"]);
  });

  it("$c -> $.", () => {    
    assertThat(tokenize("$c -> $."))
      .equalsTo(["c", "ws", "sequence", "ws", "dot"]);
  });

  it("tt $f term t $.", () => {    
    assertThat(tokenize("tt $f term t $."))
      .equalsTo(["sequence", "ws", "f", "ws", "sequence", "ws", "sequence", "ws", "dot"]);
  });

  it("weq $a wff t $.", () => {    
    assertThat(tokenize("weq $a wff t $."))
      .equalsTo(["sequence", "ws", "a", "ws", "sequence", "ws", "sequence", "ws", "dot"]);
  });

  it("${ $}", () => {    
    assertThat(tokenize("${ $}"))
      .equalsTo(["lscope", "ws", "rscope"]);
  });

  it("min $e |- P $.", () => {    
    assertThat(tokenize("min $e |- P $."))
      .equalsTo(["sequence", "ws", "e", "ws", "sequence", "ws", "sequence", "ws", "dot"]);
  });

  it("wnew $p wff s $= wr $.", () => {    
    assertThat(tokenize("wnew $p wff s $= wr $( hi $) foo $."))
      .equalsTo([
        "sequence",
        "ws",
        "p",
        "ws",
        "sequence",
        "ws",
        "sequence",
        "ws",
        "proof",
        "ws",
        "sequence",
        "ws",
        "comment",
        "ws",
        "sequence",
        "ws",
        "dot"
      ]);
  });

  it("$( hi $)", async () => {
    assertThat(tokenize("$( hi $)"))
      .equalsTo(['comment']);
  });
  
  it("$( $)", async () => {
    assertThat(tokenize("$( $)"))
      .equalsTo(['comment']);
  });
  
  it("$d a b .", async () => {
    assertThat(tokenize("$d a b ."))
      .equalsTo(['d', 'ws', 'sequence', 'ws', 'sequence', 'ws', 'sequence']);
  });
  
  it.skip("Tokenize set.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/set.mm");
    assertThat(tokenize(file.toString()).length)
      .equalsTo(8470554);
  });

  it("Compressed Proofs", async () => {
    const statement = `
     $( Relate the biconditional connective to primitive connectives.  See
        dfbi1ALT for an unusual version proved directly from axioms.
        (Contributed by NM, 29-Dec-1992.) $)

     dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
     ( wb wi wn df-bi simplim ax-mp impbi impi impbii ) ABCZABDZBADZEDEZLODZOLDE 
     ZDEPABFPQGHMNLABIJK $.
    `;
    assertThat(parse(statement).length).equalsTo(1);
  });
  
  it.skip("Parse set.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/set.mm");

    const handler = {
      feed(a) {
        // console.log(a);
      }
    };
    
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(handler)));

    const code = file.toString();

    parser.feed(code);
  }).timeout(100000);
    
  function tokenize(code) {
    const lexer = moo.compile(lexicon);
    lexer.reset(code);
    const result = [];
    do {
      const next = lexer.next();
      if (!next) {
        return result;
      }
      result.push(next.type);
    } while (true);
    return result;
  }
});

describe("Streaming", () => {
  class Reader {
    constructor() {
      this.stream = [];
      this.callbacks = [];
    }
    feed(data) {
      if (this.callbacks.length == 0) {
        this.stream.push(data);
      } else {
        let first = this.callbacks.shift();
        first(data);          
      }
    }
    async read() {
      let that = this;
      return new Promise((resolve, reject) => {
        // console.log("hi");
        if (that.stream.length == 0) {
          that.callbacks.push(resolve);
        } else {
          let first = that.stream.shift();
          resolve(first);
        }
      });
    }
  }

  it("read() then write()", async () => {
    let reader = new Reader();
    let data = reader.read();
    reader.feed("foo");
    assertThat(await data).equalsTo("foo");
  });

  it("write() then reader()", async () => {
    let reader = new Reader();
    reader.feed("foo");
    let data = reader.read();
    assertThat(await data).equalsTo("foo");
  });

  it("read() read() then write() write()", async () => {
    let reader = new Reader();
    let data1 = reader.read();
    let data2 = reader.read();
    reader.feed("foo");
    reader.feed("bar");
    assertThat(await data1).equalsTo("foo");
    assertThat(await data2).equalsTo("bar");
  });

  it("write() write() then read() read()", async () => {
    let reader = new Reader();
    reader.feed("foo");
    reader.feed("bar");
    let data1 = reader.read();
    let data2 = reader.read();
    assertThat(await data1).equalsTo("foo");
    assertThat(await data2).equalsTo("bar");
  });

  it("async tokenizer", async () => {
    const {lexicon} = require("../src/lexer.js");
    const moo = require("moo");
    const lexer = moo.compile(lexicon);
    let info;

    let reader = new Reader();

    function feed(code) {
      info = lexer.reset(code, info);

      do {
        let next = lexer.next();
        if (!next) {
          break;
        }
        reader.feed(next);
      } while (true);
    }
    
    feed("$[");

    assertThat((await reader.read()).type).equalsTo("lfile");

    feed(" filename $]");

    assertThat((await reader.read()).type).equalsTo("ws");
    assertThat((await reader.read()).type).equalsTo("sequence");
    assertThat((await reader.read()).type).equalsTo("ws");
    assertThat((await reader.read()).type).equalsTo("rfile");
  });

  
});

describe("Descent", () => {
    
  const {parse} = require("../src/descent.js");
  it("", () => {
    assertThat(parse("")).equalsTo(true);
  });

  it(" ", () => {
    assertThat(parse(" ")).equalsTo(true);
  });

  it("$[ filename $]", () => {
    assertThat(parse("$[ filename $]")).equalsTo(true);
  });

  it("$(  $)", () => {
    assertThat(parse("$( $)")).equalsTo(true);
  });

  it(" $(  $) ", () => {
    assertThat(parse(" $( $) ")).equalsTo(true);
  });

  it("$(  $)$(  $)", () => {
    assertThat(parse("$(  $)$(  $)")).equalsTo(true);
  });

  it("$(  $) $(  $)", () => {
    assertThat(parse("$(  $) $(  $)")).equalsTo(true);
  });

  it("$v p $.", () => {
    assertThat(parse("$v p $.")).equalsTo(true);
  });

  it(" $v p $.", () => {
    assertThat(parse(" $v p $.")).equalsTo(true);
  });

  it("$v p $. ", () => {
    assertThat(parse("$v p $. ")).equalsTo(true);
  });

  it("$v p q $.", () => {
    assertThat(parse("$v p q $.")).equalsTo(true);
  });

  it("$v p$.", () => {
    try {
      assertThat(parse("$v p$.")).equalsTo(true);
      throw new Error();
    } catch (e) {
      assertThat(e.message).equalsTo("Excepted a ws or a comment");
    }
  });

  it("$c ~ => ( ) $.", () => {
    assertThat(parse("$c ~ => ( ) $.")).equalsTo(true);
  });

  it("wp $f wff p $.", () => {
    assertThat(parse("wp $f wff p $.")).equalsTo(true);
  });

  it("we $a wff $.", () => {
    assertThat(parse("$( The empty sequence is a wff. $) we $a wff $.")).equalsTo(true);
  });
  
  it("wn $a wff ~ p $.", () => {
    assertThat(parse("wn $a wff ~ p $.")).equalsTo(true);
  });

  it("wi $a wff ( p => q ) $.", () => {
    assertThat(parse("wi $a wff ( p => q ) $.")).equalsTo(true);
  });

  it("t1 $p wff ~ q $= wq wn $.", () => {
    assertThat(parse("t1 $p wff ~ q $= wq wn $.")).equalsTo(true);
  });

  it("min $e |- p $.", () => {
    assertThat(parse("min $e |- p $.")).equalsTo(true);
  });

  it("maj $e |- ( p => q ) $.", () => {
    assertThat(parse("maj $e |- ( p => q ) $.")).equalsTo(true);
  });

  it("${ $}", () => {
    assertThat(parse("${ $}")).equalsTo(true);
  });

  it("${ min $e |- p $. $}", () => {
    assertThat(parse("${ min $e |- p $. $}")).equalsTo(true);
  });

  it("${ min $e |- p $. maj $e |- ( p => q ) $. ax-mp $a |- q $. $}", () => {
    assertThat(parse("${ min $e |- p $. maj $e |- ( p => q ) $. ax-mp $a |- q $. $}")).equalsTo(true);
  });

  it("mp2", () => {
    assertThat(parse(`
    $\{
      mp2.1 $e |- p $.
      mp2.2 $e |- q $.
      mp2.3 $e |- ( p => ( q => r ) ) $.
      mp2 $p |- r $=
          wq wr mp2.2 wp wq wr wi mp2.1 mp2.3 ax-mp ax-mp $.
    $\} 
    `)).equalsTo(true);
  });

  it("dfbi1", () => {
    const statement = `
     $( Relate the biconditional connective to primitive connectives.  See
        dfbi1ALT for an unusual version proved directly from axioms.
        (Contributed by NM, 29-Dec-1992.) $)

     dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
     ( wb wi wn df-bi simplim ax-mp impbi impi impbii ) ABCZABDZBADZEDEZLODZOLDE 
     ZDEPABFPQGHMNLABIJK $.
    `;
    assertThat(parse(statement)).equalsTo(true);
  });

  it("? in compressed proofs", () => {
    const statement = `
     dfbi1 $p |- a $= ( wb ) AB?CD $.
    `;
    assertThat(parse(statement)).equalsTo(true);
  });

  it.skip("miu.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/miu.mm");
    assertThat(parse(file.toString())).equalsTo(true);
  });

  it.skip("demo0.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/demo0.mm");
    assertThat(parse(file.toString())).equalsTo(true);
  });

  it("idi", () => {
    const statement = `
  $\{
    idi.1 $e |- R |= A $.
    $( The identity inference. $)
    idi $p |- R |= A $=
      (  ) C $.
      $( [9-Oct-2014] $)
  $\}
    `;
    assertThat(parse(statement)).equalsTo(true);
  });

  it("$d x R $.", () => {
    assertThat(parse("$d x R $.")).equalsTo(true);
  });

  it.skip("hol.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/hol.mm");
    assertThat(parse(file.toString())).equalsTo(true);
  });

  it.skip("set.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/set.mm");
    assertThat(parse(file.toString())).equalsTo(true);
  });

  it.skip("ql.mm", async () => {
    const fs = require("fs/promises");
    const file = await fs.readFile("tests/ql.mm");
    assertThat(parse(file.toString())).equalsTo(true);
  });

});

function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
