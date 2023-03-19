include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cjcl.mm"
include "syl.mm"

theorem cjcld
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( * ` A ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cc
    wcel
    recld.1
    cA
    cjcl
    syl
end
