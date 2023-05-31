include "wal.mm"
include "alimi.mm"
include "syl.mm"

theorem sylg
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume sylg.1: |- ( ph -> A. x ps )
  assume sylg.2: |- ( ps -> ch )


  assert |- ( ph -> A. x ch )

  proof
    wph
    wps
    vx
    wal
    wch
    vx
    wal
    sylg.1
    wps
    wch
    vx
    sylg.2
    alimi
    syl
end
