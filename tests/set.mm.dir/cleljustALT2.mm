include "weq.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "nfv.mm"
include "elequ1.mm"
include "equsexv.mm"
include "bicomi.mm"

theorem cleljustALT2
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
    nfv
    vz
    vx
    vy
    elequ1
    equsexv
    bicomi
end
