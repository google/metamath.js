include "weq.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "elequ1.mm"
include "equsexvw.mm"
include "bicomi.mm"

theorem cleljust
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x e. y <-> E. z ( z = x /\ z e. y ) )

  proof
    vz
    vx
    weq
    vz
    vy
    wel
    #
    wa
    vz
    wex
    vx
    vy
    wel
    #
    @0
    @1
    vz
    vx
    vz
    vx
    vy
    elequ1
    equsexvw
    bicomi
end
