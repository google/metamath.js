include "cv.mm"
include "wnel.mm"
include "cab.mm"
include "cvv.mm"
include "vprc.mm"
include "nelir.mm"
include "wceq.mm"
include "wb.mm"
include "ruv.mm"
include "neleq1.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem ruALT
  let vx: setvar x


  assert |- { x | x e/ x } e/ _V

  proof
    vx
    cv
    #
    @0
    wnel
    vx
    cab
    #
    cvv
    wnel
    #
    cvv
    cvv
    wnel
    #
    cvv
    cvv
    vprc
    nelir
    @1
    cvv
    wceq
    @2
    @3
    wb
    vx
    ruv
    @1
    cvv
    cvv
    neleq1
    ax-mp
    mpbir
end
