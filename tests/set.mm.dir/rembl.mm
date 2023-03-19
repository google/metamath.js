include "cr.mm"
include "c0.mm"
include "cdif.mm"
include "cvol.mm"
include "cdm.mm"
include "dif0.mm"
include "wcel.mm"
include "0mbl.mm"
include "cmmbl.mm"
include "ax-mp.mm"
include "eqeltrri.mm"

theorem rembl



  assert |- RR e. dom vol

  proof
    cr
    c0
    cdif
    #
    cr
    cvol
    cdm
    #
    cr
    dif0
    c0
    @1
    wcel
    @0
    @1
    wcel
    0mbl
    c0
    cmmbl
    ax-mp
    eqeltrri
end
