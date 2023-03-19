include "wa.mm"
include "ex.mm"
include "exp5l.mm"

theorem exp512
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp512.1: |- ( ( ph /\ ( ( ps /\ ch ) /\ ( th /\ ta ) ) ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wph
    wps
    wch
    wa
    wth
    wta
    wa
    wa
    wet
    exp512.1
    ex
    exp5l
end
