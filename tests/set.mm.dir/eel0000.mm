include "wi.mm"
include "exp41.mm"
include "mp2.mm"

theorem eel0000
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume eel0000.1: |- ph
  assume eel0000.2: |- ps
  assume eel0000.3: |- ch
  assume eel0000.4: |- th
  assume eel0000.5: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


  assert |- ta

  proof
    wch
    wth
    wta
    eel0000.3
    eel0000.4
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    eel0000.1
    eel0000.2
    wph
    wps
    wch
    wth
    wta
    eel0000.5
    exp41
    mp2
    mp2
end
