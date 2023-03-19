include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "truan.mm"
include "anidm.mm"
include "3bitri.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "syl3an3.mm"
include "sylbir.mm"

theorem eelT11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume eelT11.1: |- ( T. -> ph )
  assume eelT11.2: |- ( ps -> ch )
  assume eelT11.3: |- ( ps -> th )
  assume eelT11.4: |- ( ( ph /\ ch /\ th ) -> ta )


  assert |- ( ps -> ta )

  proof
    wps
    wtru
    wps
    wps
    w3a
    #
    wta
    @0
    wtru
    wps
    wps
    wa
    #
    wa
    @1
    wps
    wtru
    wps
    wps
    3anass
    @1
    truan
    wps
    anidm
    3bitri
    wps
    wtru
    wps
    wth
    wta
    eelT11.3
    wps
    wtru
    wch
    wth
    wta
    eelT11.2
    wtru
    wph
    wch
    wth
    wta
    eelT11.1
    eelT11.4
    syl3an1
    syl3an2
    syl3an3
    sylbir
end
