include "weu.mm"
include "wb.mm"
include "wtru.mm"
include "a1i.mm"
include "eubidv.mm"
include "trud.mm"

theorem eubii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume eubii.1: |- ( ph <-> ps )


  assert |- ( E! x ph <-> E! x ps )

  proof
    wph
    vx
    weu
    wps
    vx
    weu
    wb
    wtru
    wph
    wps
    vx
    wph
    wps
    wb
    wtru
    eubii.1
    a1i
    eubidv
    trud
end
