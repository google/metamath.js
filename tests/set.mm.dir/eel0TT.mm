include "wtru.mm"
include "wa.mm"
include "truan.mm"
include "mp3an1.mm"
include "sylan.mm"
include "sylbir.mm"
include "syl.mm"
include "trud.mm"

theorem eel0TT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume eel0TT.1: |- ph
  assume eel0TT.2: |- ( T. -> ps )
  assume eel0TT.3: |- ( T. -> ch )
  assume eel0TT.4: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- th

  proof
    wth
    wtru
    wch
    wth
    eel0TT.3
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
    eel0TT.2
    wph
    wps
    wch
    wth
    eel0TT.1
    eel0TT.4
    mp3an1
    sylan
    sylbir
    syl
    trud
end
