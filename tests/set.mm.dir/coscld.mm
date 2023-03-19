include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "coscl.mm"
include "syl.mm"

theorem coscld
  let wph: wff ph
  let cA: class A
  assume sincld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( cos ` A ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccos
    cfv
    cc
    wcel
    sincld.1
    cA
    coscl
    syl
end
