include "cv.mm"
include "wcel.mm"
include "id.mm"
include "rgen.mm"

theorem ralel
  let vx: setvar x
  let cA: class A


  assert |- A. x e. A x e. A

  proof
    vx
    cv
    cA
    wcel
    #
    vx
    cA
    @0
    id
    rgen
end
