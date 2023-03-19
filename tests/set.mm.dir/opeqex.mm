include "cop.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "neeq1.mm"
include "opnz.mm"
include "3bitr3g.mm"

theorem opeqex
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( <. A , B >. = <. C , D >. -> ( ( A e. _V /\ B e. _V ) <-> ( C e. _V /\ D e. _V ) ) )

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
    @0
    c0
    wne
    @1
    c0
    wne
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    cC
    cvv
    wcel
    cD
    cvv
    wcel
    wa
    @0
    @1
    c0
    neeq1
    cA
    cB
    opnz
    cC
    cD
    opnz
    3bitr3g
end
