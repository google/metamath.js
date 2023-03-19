include "ax-syl.mm"

theorem syl
  param tr: term R
  param ts: term S
  param tt: term T
  assume ax-syl.1: |- R |= S
  assume ax-syl.2: |- S |= T


  assert |- R |= T

  proof
    tr
    ts
    tt
    ax-syl.1
    ax-syl.2
    ax-syl
end
