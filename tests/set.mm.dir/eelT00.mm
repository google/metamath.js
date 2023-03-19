include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anass.mm"
include "truan.mm"
include "bitri.mm"
include "syl3an1.mm"
include "sylbir.mm"
include "mpan.mm"
include "ax-mp.mm"

theorem eelT00
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume eelT00.1: |- ( T. -> ph )
  assume eelT00.2: |- ps
  assume eelT00.3: |- ch
  assume eelT00.4: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- th

  proof
    wch
    wth
    eelT00.3
    wps
    wch
    wth
    eelT00.2
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
    eelT00.1
    eelT00.4
    syl3an1
    sylbir
    mpan
    ax-mp
end
