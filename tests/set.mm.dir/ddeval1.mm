include "cr.mm"
include "wss.mm"
include "cc0.mm"
include "wcel.mm"
include "cdde.mm"
include "cfv.mm"
include "c1.mm"
include "cif.mm"
include "cpw.mm"
include "wceq.mm"
include "cvv.mm"
include "reex.mm"
include "ssex.mm"
include "elpwg.mm"
include "biimpar.mm"
include "mpancom.mm"
include "cv.mm"
include "eleq2.mm"
include "ifbid.mm"
include "df-dde.mm"
include "1ex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "iftrue.mm"
include "sylan9eq.mm"

theorem ddeval1
  let cA: class A
  let va: setvar a


  assert |- ( ( A C_ RR /\ 0 e. A ) -> ( Ddelta ` A ) = 1 )

  proof
    cA
    cr
    wss
    #
    cc0
    cA
    wcel
    #
    cA
    cdde
    cfv
    #
    @1
    c1
    cc0
    cif
    #
    c1
    @0
    cA
    cr
    cpw
    #
    wcel
    #
    @2
    @3
    wceq
    cA
    cvv
    wcel
    #
    @0
    @5
    cA
    cr
    reex
    ssex
    @6
    @5
    @0
    cA
    cr
    cvv
    elpwg
    biimpar
    mpancom
    va
    cA
    cc0
    va
    cv
    #
    wcel
    #
    c1
    cc0
    cif
    @3
    @4
    cdde
    @7
    cA
    wceq
    @8
    @1
    c1
    cc0
    @7
    cA
    cc0
    eleq2
    ifbid
    va
    df-dde
    @1
    c1
    cc0
    1ex
    c0ex
    ifex
    fvmpt
    syl
    @1
    c1
    cc0
    iftrue
    sylan9eq
end
