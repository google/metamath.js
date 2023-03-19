include "hb.mm"
include "ax-cb2.mm"
include "eqtypri.mm"
include "eqcomi.mm"
include "mpbi.mm"

theorem mpbir
  let ta: term A
  let tb: term B
  let tr: term R
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
