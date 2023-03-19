include "crp.mm"
include "cr.mm"
include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "df-rp.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem rpre
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR+ -> A e. RR )

  proof
    crp
    cr
    cA
    crp
    cc0
    vx
    cv
    clt
    wbr
    #
    vx
    cr
    crab
    cr
    vx
    df-rp
    @0
    vx
    cr
    ssrab2
    eqsstri
    sseli
end
