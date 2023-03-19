include "wa.mm"
include "wi.mm"
include "imp.mm"
include "imp4c.mm"

theorem imp5g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume imp5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wi
    imp5.1
    imp
    imp4c
end
