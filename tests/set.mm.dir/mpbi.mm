include "biimpi.mm"
include "ax-mp.mm"

theorem mpbi
  param wph: wff ph
  param wps: wff ps
  assume mpbi.min: |- ph
  assume mpbi.maj: |- ( ph <-> ps )


  assert |- ps

  proof
    wph
    wps
    mpbi.min
    wph
    wps
    mpbi.maj
    biimpi
    ax-mp
end
