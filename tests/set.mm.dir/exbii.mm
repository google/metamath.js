include "wb.mm"
include "wex.mm"
include "exbi.mm"
include "mpg.mm"

theorem exbii
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume exbii.1: |- ( ph <-> ps )


  assert |- ( E. x ph <-> E. x ps )

  proof
    wph
    wps
    wb
    wph
    vx
    wex
    wps
    vx
    wex
    wb
    vx
    wph
    wps
    vx
    exbi
    exbii.1
    mpg
end
