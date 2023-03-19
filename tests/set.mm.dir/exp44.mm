include "wi.mm"
include "wa.mm"
include "exp32.mm"
include "expd.mm"

theorem exp44
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp44.1: |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta )


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
    exp44.1
    exp32
    expd
end
