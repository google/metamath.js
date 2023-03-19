include "wi.mm"
include "wa.mm"
include "ex.mm"
include "exp43.mm"

theorem exp53
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp53.1: |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wta
    wet
    exp53.1
    ex
    exp43
end
