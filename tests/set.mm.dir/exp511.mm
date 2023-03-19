include "wa.mm"
include "ex.mm"
include "exp5k.mm"

theorem exp511
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp511.1: |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et )


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
    wth
    wa
    wa
    wta
    wa
    wet
    exp511.1
    ex
    exp5k
end
