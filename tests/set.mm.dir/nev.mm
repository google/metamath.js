include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cvv.mm"
include "eqv.mm"
include "necon3abii.mm"

theorem nev
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= _V <-> -. A. x x e. A )

  proof
    vx
    cv
    cA
    wcel
    vx
    wal
    cA
    cvv
    vx
    cA
    eqv
    necon3abii
end
