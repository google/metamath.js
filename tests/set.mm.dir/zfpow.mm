include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "ax-pow.mm"
include "weq.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbi.mm"

theorem zfpow
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
  assert |- E. x A. y ( A. x ( x e. y -> x e. z ) -> y e. x )

  proof
    vw
    vy
    wel
    #
    vw
    vz
    wel
    #
    wi
    #
    vw
    wal
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
    vx
    vy
    wel
    #
    vx
    vz
    wel
    #
    wi
    #
    vx
    wal
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
    ax-pow
    @6
    @12
    vx
    @5
    @11
    vy
    @3
    @10
    @4
    @2
    @9
    vw
    vx
    vw
    vx
    weq
    @0
    @7
    @1
    @8
    vw
    vx
    vy
    elequ1
    vw
    vx
    vz
    elequ1
    imbi12d
    cbvalv
    imbi1i
    albii
    exbii
    mpbi
end
