include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "prssg.mm"
include "elprg.mm"
include "bi2anan9.mm"
include "bitr3d.mm"

theorem ssprss
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( { A , B } C_ { C , D } <-> ( ( A = C \/ A = D ) /\ ( B = C \/ B = D ) ) ) )

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
    cA
    cC
    cD
    cpr
    #
    wcel
    #
    cB
    @2
    wcel
    #
    wa
    cA
    cB
    cpr
    @2
    wss
    cA
    cC
    wceq
    cA
    cD
    wceq
    wo
    #
    cB
    cC
    wceq
    cB
    cD
    wceq
    wo
    #
    wa
    cA
    cB
    @2
    cV
    cW
    prssg
    @0
    @3
    @5
    @1
    @4
    @6
    cA
    cC
    cD
    cV
    elprg
    cB
    cC
    cD
    cW
    elprg
    bi2anan9
    bitr3d
end
