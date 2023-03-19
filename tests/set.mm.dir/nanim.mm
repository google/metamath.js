include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "nannan.mm"
include "anidmdbi.mm"
include "bitr2i.mm"

theorem nanim
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) )

  proof
    wph
    wps
    wps
    wnan
    wnan
    wph
    wps
    wps
    wa
    wi
    wph
    wps
    wi
    wph
    wps
    wps
    nannan
    wph
    wps
    anidmdbi
    bitr2i
end
