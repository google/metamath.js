include "cafv.mm"
include "wdfat.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "cvv.mm"
include "cif.mm"
include "cfv.mm"
include "df-afv.mm"
include "wceq.mm"
include "df-fv.mm"
include "eqcomi.mm"
include "ifeq1.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem dfafv2
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vk: setvar k


  assert |- ( F ''' A ) = if ( F defAt A , ( F ` A ) , _V )

  proof
    cA
    cF
    cafv
    cA
    cF
    wdfat
    #
    cA
    vx
    cv
    cF
    wbr
    vx
    cio
    #
    cvv
    cif
    #
    @0
    cA
    cF
    cfv
    #
    cvv
    cif
    #
    vx
    cA
    cF
    df-afv
    @1
    @3
    wceq
    @2
    @4
    wceq
    @3
    @1
    vx
    cA
    cF
    df-fv
    eqcomi
    @0
    @1
    @3
    cvv
    ifeq1
    ax-mp
    eqtri
end
