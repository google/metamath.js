include "hb.mm"
include "kt.mm"
include "ax-cb2.mm"
include "wtru.mm"
include "eqtru.mm"
include "eqcomi.mm"
include "ax-cb1.mm"
include "a17i.mm"
include "hbxfr.mm"

theorem hbth
  param hal: type al
  param vx: var x
  param ta: term A
  param tb: term B
  param tr: term R
  assume hbth.1: |- B : al
  assume hbth.2: |- R |= A

  disjoint R x
  assert |- R |= [ ( \ x : al . A B ) = A ]

  proof
    hal
    hb
    vx
    kt
    tb
    tr
    ta
    ta
    tr
    hbth.2
    ax-cb2
    hbth.1
    hb
    kt
    ta
    tr
    wtru
    ta
    tr
    hbth.2
    eqtru
    eqcomi
    hal
    hb
    vx
    kt
    tb
    tr
    wtru
    hbth.1
    ta
    tr
    hbth.2
    ax-cb1
    a17i
    hbxfr
end
