include "wel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "ax-reg.mm"
include "19.23bi.mm"

theorem axreg2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( x e. y -> E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) )

  proof
    vx
    vy
    wel
    #
    @0
    vz
    vx
    wel
    vz
    vy
    wel
    wn
    wi
    vz
    wal
    wa
    vx
    wex
    vx
    vy
    vx
    vz
    ax-reg
    19.23bi
end
