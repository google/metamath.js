include "wi.mm"
include "wa.mm"
include "exp31.mm"
include "expd.mm"

theorem exp42
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp42.1: |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta )


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
    exp42.1
    exp31
    expd
end
