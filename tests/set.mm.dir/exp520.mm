include "w3a.mm"
include "wa.mm"
include "ex.mm"
include "exp5o.mm"

theorem exp520
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp520.1: |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et )


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
    w3a
    wth
    wta
    wa
    wet
    exp520.1
    ex
    exp5o
end
