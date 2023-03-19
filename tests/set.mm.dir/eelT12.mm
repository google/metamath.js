include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anass.mm"
include "truan.mm"
include "bitri.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "syl3an3.mm"
include "sylbir.mm"

theorem eelT12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eelT12.1: |- ( T. -> ph )
  assume eelT12.2: |- ( ps -> ch )
  assume eelT12.3: |- ( th -> ta )
  assume eelT12.4: |- ( ( ph /\ ch /\ ta ) -> et )


  assert |- ( ( ps /\ th ) -> et )

  proof
    wps
    wth
    wa
    #
    wtru
    wps
    wth
    w3a
    #
    wet
    @1
    wtru
    @0
    wa
    @0
    wtru
    wps
    wth
    3anass
    @0
    truan
    bitri
    wth
    wtru
    wps
    wta
    wet
    eelT12.3
    wps
    wtru
    wch
    wta
    wet
    eelT12.2
    wtru
    wph
    wch
    wta
    wet
    eelT12.1
    eelT12.4
    syl3an1
    syl3an2
    syl3an3
    sylbir
end
