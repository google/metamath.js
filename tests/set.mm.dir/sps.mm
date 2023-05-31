include "wal.mm"
include "sp.mm"
include "syl.mm"

theorem sps
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
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
