include "wal.mm"
include "albii.mm"

theorem 2albii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume albii.1: |- ( ph <-> ps )


  assert |- ( A. x A. y ph <-> A. x A. y ps )

  proof
    wph
    vy
    wal
    wps
    vy
    wal
    vx
    wph
    wps
    vy
    albii.1
    albii
    albii
end
