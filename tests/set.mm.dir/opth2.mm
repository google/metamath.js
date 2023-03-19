include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "opthg2.mm"
include "mp2an.mm"

theorem opth2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opth2.1: |- C e. _V
  assume opth2.2: |- D e. _V


  assert |- ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) )

  proof
    cC
    cvv
    wcel
    cD
    cvv
    wcel
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
    cB
    cD
    wceq
    wa
    wb
    opth2.1
    opth2.2
    cA
    cB
    cC
    cD
    cvv
    cvv
    opthg2
    mp2an
end
