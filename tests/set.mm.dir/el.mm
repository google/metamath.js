include "wel.mm"
include "wi.mm"
include "wal.mm"
include "zfpow.mm"
include "weq.mm"
include "ax9.mm"
include "alrimiv.mm"
include "ax8.mm"
include "embantd.mm"
include "spimv.mm"
include "eximii.mm"

theorem el
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- E. y x e. y

  proof
    vy
    vz
    wel
    vy
    vx
    wel
    wi
    #
    vy
    wal
    #
    vz
    vy
    wel
    #
    wi
    #
    vz
    wal
    vx
    vy
    wel
    #
    vy
    vy
    vz
    vx
    zfpow
    @3
    @4
    vz
    vx
    vz
    vx
    weq
    #
    @1
    @2
    @4
    @5
    @0
    vy
    vz
    vx
    vy
    ax9
    alrimiv
    vz
    vx
    vy
    ax8
    embantd
    spimv
    eximii
end
