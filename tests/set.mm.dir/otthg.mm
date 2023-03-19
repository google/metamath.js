include "cotp.mm"
include "wceq.mm"
include "cop.mm"
include "wcel.mm"
include "w3a.mm"
include "df-ot.mm"
include "eqeq12i.mm"
include "wb.mm"
include "wa.mm"
include "cvv.mm"
include "opex.mm"
include "opthg.mm"
include "mpan.mm"
include "anbi1d.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "sylan9bbr.mm"
include "3impa.mm"
include "syl5bb.mm"

theorem otthg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( A e. U /\ B e. V /\ C e. W ) -> ( <. A , B , C >. = <. D , E , F >. <-> ( A = D /\ B = E /\ C = F ) ) )

  proof
    cA
    cB
    cC
    cotp
    #
    cD
    cE
    cF
    cotp
    #
    wceq
    cA
    cB
    cop
    #
    cC
    cop
    #
    cD
    cE
    cop
    #
    cF
    cop
    #
    wceq
    #
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    w3a
    cA
    cD
    wceq
    #
    cB
    cE
    wceq
    #
    cC
    cF
    wceq
    #
    w3a
    #
    @0
    @3
    @1
    @5
    cA
    cB
    cC
    df-ot
    cD
    cE
    cF
    df-ot
    eqeq12i
    @7
    @8
    @9
    @6
    @13
    wb
    @9
    @6
    @2
    @4
    wceq
    #
    @12
    wa
    #
    @7
    @8
    wa
    #
    @13
    @2
    cvv
    wcel
    @9
    @6
    @15
    wb
    cA
    cB
    opex
    @2
    cC
    @4
    cF
    cvv
    cW
    opthg
    mpan
    @16
    @15
    @10
    @11
    wa
    #
    @12
    wa
    @13
    @16
    @14
    @17
    @12
    cA
    cB
    cD
    cE
    cU
    cV
    opthg
    anbi1d
    @10
    @11
    @12
    df-3an
    syl6bbr
    sylan9bbr
    3impa
    syl5bb
end
