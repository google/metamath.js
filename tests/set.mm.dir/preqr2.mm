include "cpr.mm"
include "wceq.mm"
include "prcom.mm"
include "eqeq12i.mm"
include "preqr1.mm"
include "sylbi.mm"

theorem preqr2
  let cA: class A
  let cB: class B
  let cC: class C
  assume preqr1.a: |- A e. _V
  assume preqr1.b: |- B e. _V


  assert |- ( { C , A } = { C , B } -> A = B )

  proof
    cC
    cA
    cpr
    #
    cC
    cB
    cpr
    #
    wceq
    cA
    cC
    cpr
    #
    cB
    cC
    cpr
    #
    wceq
    cA
    cB
    wceq
    @0
    @2
    @1
    @3
    cC
    cA
    prcom
    cC
    cB
    prcom
    eqeq12i
    cA
    cB
    cC
    preqr1.a
    preqr1.b
    preqr1
    sylbi
end
