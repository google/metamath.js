include "wa.mm"
include "wb.mm"
include "iba.mm"
include "syl.mm"

theorem biantrud
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biantrud.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch <-> ( ch /\ ps ) ) )

  proof
    wph
    wps
    wch
    wch
    wps
    wa
    wb
    biantrud.1
    wps
    wch
    iba
    syl
end
