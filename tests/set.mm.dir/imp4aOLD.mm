include "wi.mm"
include "wa.mm"
include "impexp.mm"
include "syl6ibr.mm"

theorem imp4aOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume imp4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    wch
    wth
    wa
    wta
    wi
    imp4.1
    wch
    wth
    wta
    impexp
    syl6ibr
end
