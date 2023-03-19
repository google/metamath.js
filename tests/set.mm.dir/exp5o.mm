include "wi.mm"
include "w3a.mm"
include "expd.mm"
include "3exp.mm"

theorem exp5o
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp5o.1: |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) )


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
    w3a
    wth
    wta
    wet
    exp5o.1
    expd
    3exp
end
