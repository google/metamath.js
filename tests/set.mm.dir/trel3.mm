include "wtr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "trel.mm"
include "anim2d.mm"
include "syl5bi.mm"
include "syld.mm"

theorem trel3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( Tr A -> ( ( B e. C /\ C e. D /\ D e. A ) -> B e. A ) )

  proof
    cA
    wtr
    #
    cB
    cC
    wcel
    #
    cC
    cD
    wcel
    #
    cD
    cA
    wcel
    #
    w3a
    #
    @1
    cC
    cA
    wcel
    #
    wa
    #
    cB
    cA
    wcel
    @4
    @1
    @2
    @3
    wa
    #
    wa
    @0
    @6
    @1
    @2
    @3
    3anass
    @0
    @7
    @5
    @1
    cA
    cC
    cD
    trel
    anim2d
    syl5bi
    cA
    cB
    cC
    trel
    syld
end
