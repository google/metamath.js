include "wcel.mm"
include "cdm.mm"
include "cvv.mm"
include "dmexg.mm"
include "syl.mm"

theorem dmexd
  let wph: wff ph
  let cA: class A
  let cV: class V
  assume dmexd.1: |- ( ph -> A e. V )


  assert |- ( ph -> dom A e. _V )

  proof
    wph
    cA
    cV
    wcel
    cA
    cdm
    cvv
    wcel
    dmexd.1
    cA
    cV
    dmexg
    syl
end
