include "wal.mm"
include "19.21bi.mm"

theorem 19.21bbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume 19.21bbi.1: |- ( ph -> A. x A. y ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    vy
    wph
    wps
    vy
    wal
    vx
    19.21bbi.1
    19.21bi
    19.21bi
end
