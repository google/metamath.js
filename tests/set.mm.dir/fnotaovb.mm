include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cafv.mm"
include "wceq.mm"
include "caov.mm"
include "cotp.mm"
include "wb.mm"
include "wa.mm"
include "opelxpi.mm"
include "fnopafvb.mm"
include "sylan2.mm"
include "3impb.mm"
include "df-aov.mm"
include "eqeq1i.mm"
include "df-ot.mm"
include "eleq1i.mm"
include "3bitr4g.mm"

theorem fnotaovb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( (( C F D )) = R <-> <. C , D , R >. e. F ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    w3a
    cC
    cD
    cop
    #
    cF
    cafv
    #
    cR
    wceq
    #
    @4
    cR
    cop
    #
    cF
    wcel
    #
    cC
    cD
    cF
    caov
    #
    cR
    wceq
    cC
    cD
    cR
    cotp
    #
    cF
    wcel
    @1
    @2
    @3
    @6
    @8
    wb
    #
    @2
    @3
    wa
    @1
    @4
    @0
    wcel
    @11
    cC
    cD
    cA
    cB
    opelxpi
    @0
    @4
    cR
    cF
    fnopafvb
    sylan2
    3impb
    @9
    @5
    cR
    cC
    cD
    cF
    df-aov
    eqeq1i
    @10
    @7
    cF
    cC
    cD
    cR
    df-ot
    eleq1i
    3bitr4g
end
