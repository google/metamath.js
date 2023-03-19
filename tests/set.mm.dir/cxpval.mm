include "cc.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "ccxp.mm"
include "wa.mm"
include "simpl.mm"
include "eqeq1d.mm"
include "simpr.mm"
include "ifbid.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ifbieq12d.mm"
include "df-cxp.mm"
include "ax-1cn.mm"
include "0cn.mm"
include "keepel.mm"
include "elexi.mm"
include "fvex.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem cxpval
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A ^c B ) = if ( A = 0 , if ( B = 0 , 1 , 0 ) , ( exp ` ( B x. ( log ` A ) ) ) ) )

  proof
    vx
    vy
    cA
    cB
    cc
    cc
    vx
    cv
    #
    cc0
    wceq
    #
    vy
    cv
    #
    cc0
    wceq
    #
    c1
    cc0
    cif
    #
    @2
    @0
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cif
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    c1
    cc0
    cif
    #
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cif
    ccxp
    @0
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    #
    @1
    @8
    @4
    @7
    @10
    @13
    @16
    @0
    cA
    cc0
    @14
    @15
    simpl
    #
    eqeq1d
    @16
    @3
    @9
    c1
    cc0
    @16
    @2
    cB
    cc0
    @14
    @15
    simpr
    #
    eqeq1d
    ifbid
    @16
    @6
    @12
    ce
    @16
    @2
    cB
    @5
    @11
    cmul
    @18
    @16
    @0
    cA
    clog
    @17
    fveq2d
    oveq12d
    fveq2d
    ifbieq12d
    vx
    vy
    df-cxp
    @8
    @10
    @13
    @10
    cc
    @9
    c1
    cc0
    cc
    ax-1cn
    0cn
    keepel
    elexi
    @12
    ce
    fvex
    ifex
    ovmpt2a
end
