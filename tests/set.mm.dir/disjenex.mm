include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "simpr.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "disjen.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"

theorem disjenex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint V x
  disjoint W x
  assert |- ( ( A e. V /\ B e. W ) -> E. x ( ( A i^i x ) = (/) /\ x ~~ B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cB
    cA
    crn
    cuni
    cpw
    #
    csn
    #
    cxp
    #
    cvv
    wcel
    #
    cA
    @5
    cin
    #
    c0
    wceq
    #
    @5
    cB
    cen
    wbr
    #
    wa
    #
    cA
    vx
    cv
    #
    cin
    #
    c0
    wceq
    #
    @11
    cB
    cen
    wbr
    #
    wa
    #
    vx
    wex
    @2
    @1
    @4
    cvv
    wcel
    @6
    @0
    @1
    simpr
    @3
    snex
    cB
    @4
    cW
    cvv
    xpexg
    sylancl
    cA
    cB
    cV
    cW
    disjen
    @15
    @10
    vx
    @5
    cvv
    @11
    @5
    wceq
    #
    @13
    @8
    @14
    @9
    @16
    @12
    @7
    c0
    @11
    @5
    cA
    ineq2
    eqeq1d
    @11
    @5
    cB
    cen
    breq1
    anbi12d
    spcegv
    sylc
end
