include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjneg.mm"
include "syl.mm"

theorem cjnegd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( * ` -u A ) = -u ( * ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cneg
    ccj
    cfv
    cA
    ccj
    cfv
    cneg
    wceq
    recld.1
    cA
    cjneg
    syl
end
