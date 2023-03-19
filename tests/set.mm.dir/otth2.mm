include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "opth.mm"
include "anbi1i.mm"
include "opex.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem otth2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume otth.1: |- A e. _V
  assume otth.2: |- B e. _V
  assume otth.3: |- R e. _V


  assert |- ( <. <. A , B >. , R >. = <. <. C , D >. , S >. <-> ( A = C /\ B = D /\ R = S ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    wceq
    #
    cR
    cS
    wceq
    #
    wa
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    @3
    wa
    @0
    cR
    cop
    @1
    cS
    cop
    wceq
    @4
    @5
    @3
    w3a
    @2
    @6
    @3
    cA
    cB
    cC
    cD
    otth.1
    otth.2
    opth
    anbi1i
    @0
    cR
    @1
    cS
    cA
    cB
    opex
    otth.3
    opth
    @4
    @5
    @3
    df-3an
    3bitr4i
end
