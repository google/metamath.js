include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "opthg.mm"
include "simpl.mm"
include "syl6bi.mm"

theorem opth1g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. = <. C , D >. -> A = C ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cop
    cC
    cD
    cop
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
    @0
    cA
    cB
    cC
    cD
    cV
    cW
    opthg
    @0
    @1
    simpl
    syl6bi
end
