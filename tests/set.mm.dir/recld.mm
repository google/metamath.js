include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cr.mm"
include "recl.mm"
include "syl.mm"

theorem recld
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Re ` A ) e. RR )

  proof
    wph
    cA
    cc
    wcel
    cA
    cre
    cfv
    cr
    wcel
    recld.1
    cA
    recl
    syl
end
