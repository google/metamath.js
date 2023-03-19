include "wi.mm"
include "wa.mm"
include "ex.mm"
include "3impa.mm"

theorem ex3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ex3.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


  assert |- ( ( ph /\ ps /\ ch ) -> ( th -> ta ) )

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
    ex3.1
    ex
    3impa
end
