include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cpr.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "rneqi.mm"
include "wceq.mm"
include "rnsnopg.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "rnun.mm"
include "3eqtr4g.mm"
include "syl5eq.mm"

theorem rnpropg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ran { <. A , C >. , <. B , D >. } = { C , D } )

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
    cA
    cC
    cop
    #
    cB
    cD
    cop
    #
    cpr
    #
    crn
    @3
    csn
    #
    @4
    csn
    #
    cun
    #
    crn
    #
    cC
    cD
    cpr
    #
    @5
    @8
    @3
    @4
    df-pr
    rneqi
    @2
    @6
    crn
    #
    @7
    crn
    #
    cun
    cC
    csn
    #
    cD
    csn
    #
    cun
    @9
    @10
    @2
    @11
    @13
    @12
    @14
    @0
    @11
    @13
    wceq
    @1
    cA
    cC
    cV
    rnsnopg
    adantr
    @1
    @12
    @14
    wceq
    @0
    cB
    cD
    cW
    rnsnopg
    adantl
    uneq12d
    @6
    @7
    rnun
    cC
    cD
    df-pr
    3eqtr4g
    syl5eq
end
