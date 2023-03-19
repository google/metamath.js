include "wa.mm"
include "wi.mm"
include "imp4a.mm"
include "imp44.mm"

theorem imp511
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume imp5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et )

  proof
    wph
    wps
    wch
    wth
    wa
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    imp5.1
    imp4a
    imp44
end
