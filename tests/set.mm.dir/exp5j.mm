include "wi.mm"
include "wa.mm"
include "expd.mm"
include "exp4c.mm"

theorem exp5j
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp5j.1: |- ( ph -> ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) -> et ) )


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
    wch
    wa
    wth
    wa
    wta
    wet
    exp5j.1
    expd
    exp4c
end
