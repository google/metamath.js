include "wb.mm"
include "wal.mm"
include "albi.mm"
include "mpg.mm"

theorem albii
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume albii.1: |- ( ph <-> ps )


  assert |- ( A. x ph <-> A. x ps )

  proof
    wph
    wps
    wb
    wph
    vx
    wal
    wps
    vx
    wal
    wb
    vx
    wph
    wps
    vx
    albi
    albii.1
    mpg
end
