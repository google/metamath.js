include "wa.mm"
include "wi.mm"
include "impexpd.mm"
include "com3rgbi.mm"
include "bitr4i.mm"

theorem impexpdcom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <-> ( ps -> ( ch -> ( ph -> th ) ) ) )

  proof
    wph
    wps
    wch
    wa
    wth
    wi
    wi
    wph
    wps
    wch
    wth
    wi
    wi
    wi
    wps
    wch
    wph
    wth
    wi
    wi
    wi
    wph
    wps
    wch
    wth
    impexpd
    wps
    wch
    wph
    wth
    com3rgbi
    bitr4i
end
