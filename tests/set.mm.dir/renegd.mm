include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "reneg.mm"
include "syl.mm"

theorem renegd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Re ` -u A ) = -u ( Re ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cneg
    cre
    cfv
    cA
    cre
    cfv
    cneg
    wceq
    recld.1
    cA
    reneg
    syl
end
