include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cop.mm"
include "df-pr.mm"
include "xpeq1i.mm"
include "wceq.mm"
include "xpsng.mm"
include "3adant2.mm"
include "3adant1.mm"
include "uneq12d.mm"
include "xpundir.mm"
include "3eqtr4g.mm"
include "syl5eq.mm"

theorem xpprsng
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. W /\ C e. U ) -> ( { A , B } X. { C } ) = { <. A , C >. , <. B , C >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cU
    wcel
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cxp
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    @5
    cxp
    #
    cA
    cC
    cop
    #
    cB
    cC
    cop
    #
    cpr
    #
    @4
    @8
    @5
    cA
    cB
    df-pr
    xpeq1i
    @3
    @6
    @5
    cxp
    #
    @7
    @5
    cxp
    #
    cun
    @10
    csn
    #
    @11
    csn
    #
    cun
    @9
    @12
    @3
    @13
    @15
    @14
    @16
    @0
    @2
    @13
    @15
    wceq
    @1
    cA
    cC
    cV
    cU
    xpsng
    3adant2
    @1
    @2
    @14
    @16
    wceq
    @0
    cB
    cC
    cW
    cU
    xpsng
    3adant1
    uneq12d
    @6
    @7
    @5
    xpundir
    @10
    @11
    df-pr
    3eqtr4g
    syl5eq
end
