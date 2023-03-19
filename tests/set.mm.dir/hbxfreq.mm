include "cv.mm"
include "wcel.mm"
include "eleq2i.mm"
include "hbxfrbi.mm"

theorem hbxfreq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume hbxfr.1: |- A = B
  assume hbxfr.2: |- ( y e. B -> A. x y e. B )


  assert |- ( y e. A -> A. x y e. A )

  proof
    vy
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    vx
    cA
    cB
    @0
    hbxfr.1
    eleq2i
    hbxfr.2
    hbxfrbi
end
