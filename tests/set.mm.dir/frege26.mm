include "wi.mm"
include "ax-frege1.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege26
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ps ) )

  proof
    wps
    wph
    wps
    wi
    wi
    wph
    wps
    wps
    wi
    wi
    wps
    wph
    ax-frege1
    wps
    wph
    wps
    ax-frege8
    ax-mp
end
