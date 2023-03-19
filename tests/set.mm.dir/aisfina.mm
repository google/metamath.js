include "wn.mm"
include "wfal.mm"
include "wb.mm"
include "nbfal.mm"
include "mpbir.mm"

theorem aisfina
  let wph: wff ph
  let vk: setvar k
  let vx: setvar x
  assume aisfina.1: |- ( ph <-> F. )


  assert |- -. ph

  proof
    wph
    wn
    wph
    wfal
    wb
    aisfina.1
    wph
    nbfal
    mpbir
end
