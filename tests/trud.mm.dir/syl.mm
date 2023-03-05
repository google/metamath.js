include "ax-syl.mm"

theorem syl
  let tr: term R
  let ts: term S
  let tt: term T
  assume ax-syl.1: |- R |= S
  assume ax-syl.2: |- S |= T


  assert |- R |= T

  step 0) tr(): term R
  step 1) ts(): term S
  step 2) tt(): term T
  step 3) ax-syl.1(): |- R |= S
  step 4) ax-syl.2(): |- S |= T
  step 5) ax-syl(0, 1, 2, 3, 4): |- R |= T
end
