include "bicomi.mm"
include "biimpi.mm"

theorem biimpri
  let wph: wff ph
  let wps: wff ps
  assume biimpri.1: |- ( ph <-> ps )


  assert |- ( ps -> ph )

  proof
    wps
    wph
    wph
    wps
    biimpri.1
    bicomi
    biimpi
end
