include "wal.mm"
include "sp.mm"
include "syl.mm"

theorem sps
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume sps.1: |- ( ph -> ps )


  assert |- ( A. x ph -> ps )

  proof
    wph
    vx
    wal
    wph
    wps
    wph
    vx
    sp
    sps.1
    syl
end
