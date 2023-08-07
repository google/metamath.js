> This is not an officially supported Google product

Metamath.js is an independent metamath verifier written in JS so that it can run in browsers.

It comes with a parser, a verifier and a renderer.

It also comes with a few experimental extensions to the language around modularization.

# Examples

- [Schönfinkel's SK](https://code.sgo.to/2023/03/23/sk.html)
- [Hofstader's MIU](https://code.sgo.to/2022/04/12/hofstadter-miu.html)
- [Hofstader's PQ](https://code.sgo.to/2022/04/13/hofstadter-pq.html)
- [2 + 2 = 4?](https://code.sgo.to/2022/11/26/2p2e4.html)
- [Verifying Set.mm](https://code.sgo.to/2022/11/26/set.mm.html)

# API

## Parser

The Parser API takes as input a metamath source and calls a handler as it produces the AST:

```js
> const {parse} = require("./src/descent.js");
> parse("$c a $. $v b $.", {feed(statement) { console.log(statement); }})
[ '$c', [ 'a' ] ]
[ '$v', [ 'b' ] ]
```

## Verifer

The Verifier API takes as input a metamath source and verifies the statements. It uses the Parser internally:

```js
> const {Verifier} = require("./src/descent.js");
> new Verifier().verify("$c a $. $v b $.");
0
```

## Compression

The Compression API manages decompressing (and compressing) proofs using the metamath compressed proof format:

```js
> const {Decompressor} = require("./src/metamath.js")
> const compressed = "AAABZBZFAACAFABBGFBAFCAFADEE";
> const integers = new Decompressor().decode(compressed)
[
  1, 1, 1, 2, -1, 2, -1, 6,
  1, 1, 3, 1,  6, 1,  2, 2,
  7, 6, 2, 1,  6, 3,  1, 6,
  1, 4, 5, 5
]
> const local = ["wph"];
> const external = "wi ax-1 ax-2 ax-mp".split(" ");
> const steps = new Decompressor().decompress(local, external, compressed)
> steps
[
  'wph', 'wph',  'wph',   'wi',
  -1,    'wi',   -1,      0,
  'wph', 'wph',  'ax-1',  'wph',
  0,     'wph',  'wi',    'wi',
  1,     0,      'wi',    'wph',
  0,     'ax-1', 'wph',   0,
  'wph', 'ax-2', 'ax-mp', 'ax-mp'
]
> new Compressor(local, steps).compress();
'AAABZBZFAACAFABBGFBAFCAFADEE'
```

# Development

```
git clone https://github.com/google/metamath.js
git cd metamath.js
npm install
npm test
```


