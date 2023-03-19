
axiom ax-syl
  let tr: term R
  let ts: term S
  let tt: term T
  assume ax-syl.1: |- R |= S
  assume ax-syl.2: |- S |= T
  assert |- R |= T
end
