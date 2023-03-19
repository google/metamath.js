include "wtru.mm"
include "wa.mm"
include "truan.mm"
include "w3a.mm"
include "3anass.mm"
include "bitri.mm"
include "syl3an1.mm"
include "sylbir.mm"
include "sylan.mm"
include "syl.mm"
include "trud.mm"

theorem eelTTT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume eelTTT.1: |- ( T. -> ph )
  assume eelTTT.2: |- ( T. -> ps )
  assume eelTTT.3: |- ( T. -> ch )
  assume eelTTT.4: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- th

  proof
    wth
    wtru
    wch
    wth
    eelTTT.3
    wch
    wtru
    wch
    wa
    wth
    wch
    truan
    wtru
    wps
    wch
    wth
    eelTTT.2
    wps
    wch
    wa
    #
    wtru
    wps
    wch
    w3a
    #
    wth
    @1
    wtru
    @0
    wa
    @0
    wtru
    wps
    wch
    3anass
    @0
    truan
    bitri
    wtru
    wph
    wps
    wch
    wth
    eelTTT.1
    eelTTT.4
    syl3an1
    sylbir
    sylan
    sylbir
    syl
    trud
end
