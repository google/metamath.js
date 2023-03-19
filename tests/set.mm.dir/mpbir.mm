include "biimpri.mm"
include "ax-mp.mm"

theorem mpbir
  param wph: wff ph
  param wps: wff ps
  assume mpbir.min: |- ps
  assume mpbir.maj: |- ( ph <-> ps )


  assert |- ph

  proof
    wps
    wph
    mpbir.min
    wph
    wps
    mpbir.maj
    biimpri
    ax-mp
end
