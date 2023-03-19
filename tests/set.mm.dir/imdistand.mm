include "wi.mm"
include "wa.mm"
include "imdistan.mm"
include "sylib.mm"

theorem imdistand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume imdistand.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wi
    wps
    wch
    wa
    wps
    wth
    wa
    wi
    imdistand.1
    wps
    wch
    wth
    imdistan
    sylib
end
