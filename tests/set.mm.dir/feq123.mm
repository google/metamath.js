include "wceq.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "feq123d.mm"

theorem feq123
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G


  assert |- ( ( F = G /\ A = C /\ B = D ) -> ( F : A --> B <-> G : C --> D ) )

  proof
    cF
    cG
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    w3a
    cA
    cC
    cB
    cD
    cF
    cG
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    feq123d
end
