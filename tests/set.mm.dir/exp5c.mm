include "wi.mm"
include "wa.mm"
include "exp4a.mm"
include "expd.mm"

theorem exp5c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp5c.1: |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wph
    wps
    wch
    wa
    wth
    wta
    wet
    exp5c.1
    exp4a
    expd
end
