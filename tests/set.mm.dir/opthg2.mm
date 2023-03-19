include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "opthg.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "3bitr4g.mm"

theorem opthg2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( C e. V /\ D e. W ) -> ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) )

  proof
    cC
    cV
    wcel
    cD
    cW
    wcel
    wa
    cC
    cD
    cop
    #
    cA
    cB
    cop
    #
    wceq
    cC
    cA
    wceq
    #
    cD
    cB
    wceq
    #
    wa
    @1
    @0
    wceq
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    cC
    cD
    cA
    cB
    cV
    cW
    opthg
    @1
    @0
    eqcom
    @4
    @2
    @5
    @3
    cA
    cC
    eqcom
    cB
    cD
    eqcom
    anbi12i
    3bitr4g
end
