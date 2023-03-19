include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cima.mm"
include "cun.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "fnsnfv.mm"
include "3adant3.mm"
include "3adant2.mm"
include "uneq12d.mm"
include "eqcomd.mm"
include "df-pr.mm"
include "imaeq2i.mm"
include "imaundi.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem fnimapr
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F Fn A /\ B e. A /\ C e. A ) -> ( F " { B , C } ) = { ( F ` B ) , ( F ` C ) } )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    w3a
    #
    cF
    cB
    csn
    #
    cima
    #
    cF
    cC
    csn
    #
    cima
    #
    cun
    #
    cB
    cF
    cfv
    #
    csn
    #
    cC
    cF
    cfv
    #
    csn
    #
    cun
    #
    cF
    cB
    cC
    cpr
    #
    cima
    #
    @9
    @11
    cpr
    @3
    @13
    @8
    @3
    @10
    @5
    @12
    @7
    @0
    @1
    @10
    @5
    wceq
    @2
    cA
    cB
    cF
    fnsnfv
    3adant3
    @0
    @2
    @12
    @7
    wceq
    @1
    cA
    cC
    cF
    fnsnfv
    3adant2
    uneq12d
    eqcomd
    @15
    cF
    @4
    @6
    cun
    #
    cima
    @8
    @14
    @16
    cF
    cB
    cC
    df-pr
    imaeq2i
    cF
    @4
    @6
    imaundi
    eqtri
    @9
    @11
    df-pr
    3eqtr4g
end
