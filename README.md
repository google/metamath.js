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

```js
> const {parse} = require("./src/descent.js");
> parse("$c a $. $v b $.", {feed(statement) { console.log(statement); }})
[ '$c', [ 'a' ] ]
[ '$v', [ 'b' ] ]
```

## Verifer

```js
> const {Verifier} = require("./src/descent.js");
> new Verifier().verify("$c a $. $v b $.");
0
```

# Development

```
git clone https://github.com/google/metamath.js
git cd metamath.js
npm install
npm test
```


