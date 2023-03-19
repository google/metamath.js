include "hb.mm"
include "ax-cb2.mm"
include "eqtypri.mm"
include "eqcomi.mm"
include "mpbi.mm"

theorem mpbir
  param ta: term A
  param tb: term B
  param tr: term R
  assume mpbir.1: |- R |= A
  assume mpbir.2: |- R |= [ B = A ]


  assert |- R |= B

  proof
    ta
    tb
    tr
    mpbir.1
    hb
    tb
    ta
    tr
    hb
    ta
    tb
    tr
    ta
    tr
    mpbir.1
    ax-cb2
    mpbir.2
    eqtypri
    mpbir.2
    eqcomi
    mpbi
end
