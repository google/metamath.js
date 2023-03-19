include "wtru.mm"
include "wa.mm"
include "truan.mm"
include "sylan.mm"
include "sylbir.mm"
include "syl.mm"
include "trud.mm"

theorem eelTT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume eelTT.1: |- ( T. -> ph )
  assume eelTT.2: |- ( T. -> ps )
  assume eelTT.3: |- ( ( ph /\ ps ) -> ch )


  assert |- ch

  proof
    wch
    wtru
    wps
    wch
    eelTT.2
    wps
    wtru
    wps
    wa
    wch
    wps
    truan
    wtru
    wph
    wps
    wch
    eelTT.1
    eelTT.3
    sylan
    sylbir
    syl
    trud
end
