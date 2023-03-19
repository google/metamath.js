include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "truan.mm"
include "simpr.mm"
include "jctl.mm"
include "impbii.mm"
include "3bitri.mm"
include "syl3an1.mm"
include "syl3an3.mm"
include "sylbir.mm"

theorem eelT01
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume eelT01.1: |- ( T. -> ph )
  assume eelT01.2: |- ps
  assume eelT01.3: |- ( ch -> th )
  assume eelT01.4: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ch -> ta )

  proof
    wch
    wtru
    wps
    wch
    w3a
    #
    wta
    @0
    wtru
    wps
    wch
    wa
    #
    wa
    @1
    wch
    wtru
    wps
    wch
    3anass
    @1
    truan
    @1
    wch
    wps
    wch
    simpr
    wch
    wps
    eelT01.2
    jctl
    impbii
    3bitri
    wch
    wtru
    wps
    wth
    wta
    eelT01.3
    wtru
    wph
    wps
    wth
    wta
    eelT01.1
    eelT01.4
    syl3an1
    syl3an3
    sylbir
end
