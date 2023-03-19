

axiom ax-syl
  param tr: term R
  param ts: term S
  param tt: term T
  assume ax-syl.1: |- R |= S
  assume ax-syl.2: |- S |= T
  assert |- R |= T
end
