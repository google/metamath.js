include "wi.mm"
include "wa.mm"
include "expd.mm"
include "ex.mm"

theorem exp4b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp4b.1: |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    wph
    wps
    wa
    wch
    wth
    wta
    exp4b.1
    expd
    ex
end
