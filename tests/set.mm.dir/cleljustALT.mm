include "weq.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "ax-5.mm"
include "elequ1.mm"
include "equsexhv.mm"
include "bicomi.mm"

theorem cleljustALT
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
    @1
    vz
    ax-5
    vz
    vx
    vy
    elequ1
    equsexhv
    bicomi
end
