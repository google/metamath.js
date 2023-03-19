include "ax-1.mm"
include "impbid21d.mm"

theorem pm5.1im
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ( ph <-> ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wps
    wph
    ax-1
    wph
    wps
    ax-1
    impbid21d
end
