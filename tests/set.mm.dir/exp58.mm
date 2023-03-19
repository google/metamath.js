include "wa.mm"
include "ex.mm"
include "exp5g.mm"

theorem exp58
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp58.1: |- ( ( ( ph /\ ps ) /\ ( ( ch /\ th ) /\ ta ) ) -> et )


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
    wa
    wch
    wth
    wa
    wta
    wa
    wet
    exp58.1
    ex
    exp5g
end
