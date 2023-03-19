include "wb.mm"
include "wnf.mm"
include "nfbiit.mm"
include "mpg.mm"

theorem nfbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfbii.1: |- ( ph <-> ps )


  assert |- ( F/ x ph <-> F/ x ps )

  proof
    wph
    wps
    wb
    wph
    vx
    wnf
    wps
    vx
    wnf
    wb
    vx
    wph
    wps
    vx
    nfbiit
    nfbii.1
    mpg
end
