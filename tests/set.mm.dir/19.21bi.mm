include "wal.mm"
include "sp.mm"
include "syl.mm"

theorem 19.21bi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.21bi.1: |- ( ph -> A. x ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    vx
    wal
    wps
    19.21bi.1
    wps
    vx
    sp
    syl
end
