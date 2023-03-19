include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cjmulge0.mm"
include "syl.mm"

theorem cjmulge0d
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> 0 <_ ( A x. ( * ` A ) ) )

  proof
    wph
    cA
    cc
    wcel
    cc0
    cA
    cA
    ccj
    cfv
    cmul
    co
    cle
    wbr
    recld.1
    cA
    cjmulge0
    syl
end
