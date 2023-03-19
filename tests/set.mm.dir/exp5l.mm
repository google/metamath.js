include "wa.mm"
include "expd.mm"
include "exp5c.mm"

theorem exp5l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp5l.1: |- ( ph -> ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) )


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
    wet
    exp5l.1
    expd
    exp5c
end
