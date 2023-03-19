include "wb.mm"
include "wex.mm"
include "exbi.mm"
include "mpg.mm"

theorem exbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
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
