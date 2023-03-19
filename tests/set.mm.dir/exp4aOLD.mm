include "wa.mm"
include "wi.mm"
include "impexp.mm"
include "syl6ib.mm"

theorem exp4aOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp4aOLD.1: |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wa
    wta
    wi
    wch
    wth
    wta
    wi
    wi
    exp4aOLD.1
    wch
    wth
    wta
    impexp
    syl6ib
end
