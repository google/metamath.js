include "wtru.mm"
include "syl.mm"
include "trud.mm"

theorem eelT
  let wph: wff ph
  let wps: wff ps
  assume eelT.1: |- ( T. -> ph )
  assume eelT.2: |- ( ph -> ps )


  assert |- ps

  proof
    wps
    wtru
    wph
    wps
    eelT.1
    eelT.2
    syl
    trud
end
