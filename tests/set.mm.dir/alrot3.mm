include "wal.mm"
include "alcom.mm"
include "albii.mm"
include "bitri.mm"

theorem alrot3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x A. y A. z ph <-> A. y A. z A. x ph )

  proof
    wph
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @0
    vx
    wal
    #
    vy
    wal
    wph
    vx
    wal
    vz
    wal
    #
    vy
    wal
    @0
    vx
    vy
    alcom
    @1
    @2
    vy
    wph
    vx
    vz
    alcom
    albii
    bitri
end
