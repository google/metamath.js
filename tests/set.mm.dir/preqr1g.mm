include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "preq1b.mm"
include "biimpd.mm"

theorem preqr1g
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( { A , C } = { B , C } -> A = B ) )

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
    #
    cA
    cC
    cpr
    cB
    cC
    cpr
    wceq
    cA
    cB
    wceq
    @2
    cA
    cB
    cC
    cV
    cW
    @0
    @1
    simpl
    @0
    @1
    simpr
    preq1b
    biimpd
end
