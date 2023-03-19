include "bj-c2uple.mm"
include "wceq.mm"
include "wa.mm"
include "bj-cpr1.mm"
include "bj-pr1eq.mm"
include "bj-pr21val.mm"
include "3eqtr3g.mm"
include "bj-cpr2.mm"
include "bj-pr2eq.mm"
include "bj-pr22val.mm"
include "jca.mm"
include "bj-2upleq.mm"
include "imp.mm"
include "impbii.mm"

theorem bj-2uplth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( (| A ,, B |) = (| C ,, D |) <-> ( A = C /\ B = D ) )

  proof
    cA
    cB
    bj-c2uple
    #
    cC
    cD
    bj-c2uple
    #
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
    wa
    @2
    @3
    @4
    @2
    @0
    bj-cpr1
    @1
    bj-cpr1
    cA
    cC
    @0
    @1
    bj-pr1eq
    cA
    cB
    bj-pr21val
    cC
    cD
    bj-pr21val
    3eqtr3g
    @2
    @0
    bj-cpr2
    @1
    bj-cpr2
    cB
    cD
    @0
    @1
    bj-pr2eq
    cA
    cB
    bj-pr22val
    cC
    cD
    bj-pr22val
    3eqtr3g
    jca
    @3
    @4
    @2
    cA
    cC
    cB
    cD
    bj-2upleq
    imp
    impbii
end
