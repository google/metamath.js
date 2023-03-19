include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "wne.mm"
include "wo.mm"
include "wb.mm"
include "opthneg.mm"
include "mp2an.mm"

theorem opthne
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opthne.1: |- A e. _V
  assume opthne.2: |- B e. _V


  assert |- ( <. A , B >. =/= <. C , D >. <-> ( A =/= C \/ B =/= D ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    cC
    cD
    cop
    wne
    cA
    cC
    wne
    cB
    cD
    wne
    wo
    wb
    opthne.1
    opthne.2
    cA
    cB
    cC
    cD
    cvv
    cvv
    opthneg
    mp2an
end
