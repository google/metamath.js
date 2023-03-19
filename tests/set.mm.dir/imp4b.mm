include "wa.mm"
include "wi.mm"
include "imp.mm"
include "impd.mm"

theorem imp4b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume imp4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    imp4.1
    imp
    impd
end
