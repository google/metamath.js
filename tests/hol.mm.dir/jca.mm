include "ax-jca.mm"

theorem jca
  param tr: term R
  param ts: term S
  param tt: term T
  assume ax-jca.1: |- R |= S
  assume ax-jca.2: |- R |= T


  assert |- R |= ( S , T )

  proof
    tr
    ts
    tt
    ax-jca.1
    ax-jca.2
    ax-jca
end
