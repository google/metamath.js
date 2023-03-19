include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "weu.mm"
include "eueq.mm"
include "mpbi.mm"

theorem eueq1
  let vx: setvar x
  let cA: class A
  assume eueq1.1: |- A e. _V

  disjoint A x
  assert |- E! x x = A

  proof
    cA
    cvv
    wcel
    vx
    cv
    cA
    wceq
    vx
    weu
    eueq1.1
    vx
    cA
    eueq
    mpbi
end
