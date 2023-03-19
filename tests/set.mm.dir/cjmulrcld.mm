include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "cjmulrcl.mm"
include "syl.mm"

theorem cjmulrcld
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A x. ( * ` A ) ) e. RR )

  proof
    wph
    cA
    cc
    wcel
    cA
    cA
    ccj
    cfv
    cmul
    co
    cr
    wcel
    recld.1
    cA
    cjmulrcl
    syl
end
