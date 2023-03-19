include "cima.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cin.mm"
include "cec.mm"
include "wceq.mm"
include "simpr.mm"
include "snssd.mm"
include "df-ss.mm"
include "sylib.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "imass2.mm"
include "syl.mm"
include "simpl.mm"
include "sstrd.mm"
include "eqtr2d.mm"
include "imainrect.mm"
include "syl6eqr.mm"
include "df-ec.mm"
include "3eqtr4g.mm"

theorem ecinxp
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( ( R " A ) C_ A /\ B e. A ) -> [ B ] R = [ B ] ( R i^i ( A X. A ) ) )

  proof
    cR
    cA
    cima
    #
    cA
    wss
    #
    cB
    cA
    wcel
    #
    wa
    #
    cR
    cB
    csn
    #
    cima
    #
    cR
    cA
    cA
    cxp
    cin
    #
    @4
    cima
    #
    cB
    cR
    cec
    cB
    @6
    cec
    @3
    @5
    cR
    @4
    cA
    cin
    #
    cima
    #
    cA
    cin
    #
    @7
    @3
    @10
    @5
    cA
    cin
    #
    @5
    @3
    @9
    @5
    cA
    @3
    @8
    @4
    cR
    @3
    @4
    cA
    wss
    #
    @8
    @4
    wceq
    @3
    cB
    cA
    @1
    @2
    simpr
    snssd
    #
    @4
    cA
    df-ss
    sylib
    imaeq2d
    ineq1d
    @3
    @5
    cA
    wss
    @11
    @5
    wceq
    @3
    @5
    @0
    cA
    @3
    @12
    @5
    @0
    wss
    @13
    @4
    cA
    cR
    imass2
    syl
    @1
    @2
    simpl
    sstrd
    @5
    cA
    df-ss
    sylib
    eqtr2d
    cA
    cA
    cR
    @4
    imainrect
    syl6eqr
    cB
    cR
    df-ec
    cB
    @6
    df-ec
    3eqtr4g
end
