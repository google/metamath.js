include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "anabs5.mm"
include "truan.mm"
include "3bitri.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "syl3an3.mm"
include "sylbir.mm"

theorem eelTT1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume eelTT1.1: |- ( T. -> ph )
  assume eelTT1.2: |- ( T. -> ps )
  assume eelTT1.3: |- ( ch -> th )
  assume eelTT1.4: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ch -> ta )

  proof
    wch
    wtru
    wtru
    wch
    w3a
    #
    wta
    @0
    wtru
    wtru
    wch
    wa
    #
    wa
    @1
    wch
    wtru
    wtru
    wch
    3anass
    wtru
    wch
    anabs5
    wch
    truan
    3bitri
    wch
    wtru
    wtru
    wth
    wta
    eelTT1.3
    wtru
    wtru
    wps
    wth
    wta
    eelTT1.2
    wtru
    wph
    wps
    wth
    wta
    eelTT1.1
    eelTT1.4
    syl3an1
    syl3an2
    syl3an3
    sylbir
end
