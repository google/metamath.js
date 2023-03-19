include "weq.mm"
include "wel.mm"
include "elequ1.mm"
include "elequ2.mm"
include "sylan9bb.mm"

theorem bj-elequ12
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t


  assert |- ( ( x = y /\ z = t ) -> ( x e. z <-> y e. t ) )

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
    elequ1
    vz
    vt
    vy
    elequ2
    sylan9bb
end
