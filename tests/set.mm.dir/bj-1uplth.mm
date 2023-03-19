include "bj-c1upl.mm"
include "wceq.mm"
include "bj-cpr1.mm"
include "bj-pr1eq.mm"
include "bj-pr11val.mm"
include "3eqtr3g.mm"
include "bj-1upleq.mm"
include "impbii.mm"

theorem bj-1uplth
  let cA: class A
  let cB: class B


  assert |- ( (| A |) = (| B |) <-> A = B )

  proof
    cA
    bj-c1upl
    #
    cB
    bj-c1upl
    #
    wceq
    #
    cA
    cB
    wceq
    @2
    @0
    bj-cpr1
    @1
    bj-cpr1
    cA
    cB
    @0
    @1
    bj-pr1eq
    cA
    bj-pr11val
    cB
    bj-pr11val
    3eqtr3g
    cA
    cB
    bj-1upleq
    impbii
end
