include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "ax-un.mm"
include "weq.mm"
include "elequ2.mm"
include "elequ1.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbi.mm"

theorem zfun
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x )

  proof
    vy
    vw
    wel
    #
    vw
    vz
    wel
    #
    wa
    #
    vw
    wex
    #
    vy
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    vx
    wex
    @4
    vx
    vz
    wel
    #
    wa
    #
    vx
    wex
    #
    @4
    wi
    #
    vy
    wal
    #
    vx
    wex
    vz
    vx
    vy
    vw
    ax-un
    @6
    @11
    vx
    @5
    @10
    vy
    @3
    @9
    @4
    @2
    @8
    vw
    vx
    vw
    vx
    weq
    @0
    @4
    @1
    @7
    vw
    vx
    vy
    elequ2
    vw
    vx
    vz
    elequ1
    anbi12d
    cbvexv
    imbi1i
    albii
    exbii
    mpbi
end
