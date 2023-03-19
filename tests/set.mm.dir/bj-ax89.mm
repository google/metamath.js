include "weq.mm"
include "wel.mm"
include "ax8.mm"
include "ax9.mm"
include "sylan9.mm"

theorem bj-ax89
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t


  assert |- ( ( x = y /\ z = t ) -> ( x e. z -> y e. t ) )

  proof
    vx
    vy
    weq
    vx
    vz
    wel
    vy
    vz
    wel
    vz
    vt
    weq
    vy
    vt
    wel
    vx
    vy
    vz
    ax8
    vz
    vt
    vy
    ax9
    sylan9
end
