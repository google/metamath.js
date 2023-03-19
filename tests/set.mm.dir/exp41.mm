include "wi.mm"
include "wa.mm"
include "ex.mm"
include "exp31.mm"

theorem exp41
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume exp41.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


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
    wa
    wch
    wa
    wth
    wta
    exp41.1
    ex
    exp31
end
