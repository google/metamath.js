include "ax-syl.mm"

theorem syl
  let tr: term R
  let ts: term S
  let tt: term T
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
