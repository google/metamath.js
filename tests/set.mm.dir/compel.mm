include "cv.mm"
include "cvv.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"

theorem compel
  let vx: setvar x
  let cA: class A


  assert |- ( x e. ( _V \ A ) <-> -. x e. A )

  proof
    vx
    cv
    #
    cvv
    cA
    cdif
    wcel
    @0
    cvv
    wcel
    @0
    cA
    wcel
    wn
    vx
    vex
    @0
    cvv
    cA
    eldif
    mpbiran
end
