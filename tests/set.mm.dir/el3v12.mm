include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "el3v1.mm"
include "el2v1.mm"

theorem el3v12
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  assume el3v12.1: |- ( ( x e. _V /\ y e. _V /\ ch ) -> th )


  assert |- ( ch -> th )

  proof
    wch
    wth
    vy
    vy
    cv
    cvv
    wcel
    wch
    wth
    vx
    el3v12.1
    el3v1
    el2v1
end
