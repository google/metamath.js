include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "cvv.mm"
include "cdif.mm"
include "compel.mm"
include "abbi2i.mm"

theorem compeq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( _V \ A ) = { x | -. x e. A }

  proof
    vx
    cv
    cA
    wcel
    wn
    vx
    cvv
    cA
    cdif
    vx
    cA
    compel
    abbi2i
end
