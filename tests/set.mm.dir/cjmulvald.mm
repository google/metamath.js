include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "c2.mm"
include "cexp.mm"
include "cim.mm"
include "caddc.mm"
include "wceq.mm"
include "cjmulval.mm"
include "syl.mm"

theorem cjmulvald
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A x. ( * ` A ) ) = ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) )

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
    cA
    cre
    cfv
    c2
    cexp
    co
    cA
    cim
    cfv
    c2
    cexp
    co
    caddc
    co
    wceq
    recld.1
    cA
    cjmulval
    syl
end
