include "wtru.mm"
include "wb.mm"
include "tbtru.mm"
include "mpbir.mm"

theorem aistia
  let wph: wff ph
  let vk: setvar k
  let vx: setvar x
  assume aistia.1: |- ( ph <-> T. )


  assert |- ph

  proof
    wph
    wph
    wtru
    wb
    aistia.1
    wph
    tbtru
    mpbir
end
