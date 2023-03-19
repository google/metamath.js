include "wa.mm"
include "ex.mm"
include "exp5d.mm"

theorem exp56
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp56.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ ( th /\ ta ) ) -> et )


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
    wa
    wth
    wta
    wa
    wet
    exp56.1
    ex
    exp5d
end
