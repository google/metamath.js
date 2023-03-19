include "wal.mm"
include "2albii.mm"
include "albii.mm"

theorem 3albii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume 3albii.1: |- ( ph <-> ps )


  assert |- ( A. x A. y A. z ph <-> A. x A. y A. z ps )

  proof
    wph
    vz
    wal
    vy
    wal
    wps
    vz
    wal
    vy
    wal
    vx
    wph
    wps
    vy
    vz
    3albii.1
    2albii
    albii
end
