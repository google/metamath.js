include "wal.mm"
include "alrot3.mm"
include "albii.mm"
include "bitri.mm"

theorem alrot4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph )

  proof
    wph
    vw
    wal
    vz
    wal
    vy
    wal
    #
    vx
    wal
    wph
    vy
    wal
    #
    vw
    wal
    vz
    wal
    #
    vx
    wal
    @1
    vx
    wal
    vw
    wal
    vz
    wal
    @0
    @2
    vx
    wph
    vy
    vz
    vw
    alrot3
    albii
    @1
    vx
    vz
    vw
    alrot3
    bitri
end
