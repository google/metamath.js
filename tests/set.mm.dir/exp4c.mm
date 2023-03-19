include "wi.mm"
include "wa.mm"
include "expd.mm"

theorem exp4c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp4c.1: |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wph
    wps
    wch
    wa
    wth
    wta
    exp4c.1
    expd
    expd
end
