include "wa.mm"
include "wb.mm"
include "ibar.mm"
include "syl.mm"

theorem biantrurd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biantrud.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch <-> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wch
    wps
    wch
    wa
    wb
    biantrud.1
    wps
    wch
    ibar
    syl
end
