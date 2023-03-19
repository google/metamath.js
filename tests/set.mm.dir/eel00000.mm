include "wi.mm"
include "wa.mm"
include "exp41.mm"
include "mpan.mm"
include "mp2.mm"

theorem eel00000
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel00000.1: |- ph
  assume eel00000.2: |- ps
  assume eel00000.3: |- ch
  assume eel00000.4: |- th
  assume eel00000.5: |- ta
  assume eel00000.6: |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> et )


  assert |- et

  proof
    wth
    wta
    wet
    eel00000.4
    eel00000.5
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    #
    eel00000.2
    eel00000.3
    wph
    wps
    wch
    @0
    wi
    eel00000.1
    wph
    wps
    wa
    wch
    wth
    wta
    wet
    eel00000.6
    exp41
    mpan
    mp2
    mp2
end
