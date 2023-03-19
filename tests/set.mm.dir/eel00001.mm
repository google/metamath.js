include "wi.mm"
include "wa.mm"
include "exp41.mm"
include "mp2an.mm"
include "mp2.mm"
include "syl.mm"

theorem eel00001
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume eel00001.1: |- ph
  assume eel00001.2: |- ps
  assume eel00001.3: |- ch
  assume eel00001.4: |- th
  assume eel00001.5: |- ( ta -> et )
  assume eel00001.6: |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ et ) -> ze )


  assert |- ( ta -> ze )

  proof
    wta
    wet
    wze
    eel00001.5
    wch
    wth
    wet
    wze
    wi
    #
    eel00001.3
    eel00001.4
    wph
    wps
    wch
    wth
    @0
    wi
    wi
    eel00001.1
    eel00001.2
    wph
    wps
    wa
    wch
    wth
    wet
    wze
    eel00001.6
    exp41
    mp2an
    mp2
    syl
end
