include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "remim.mm"
include "syl.mm"

theorem remimd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( * ` A ) = ( ( Re ` A ) - ( _i x. ( Im ` A ) ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cA
    cre
    cfv
    ci
    cA
    cim
    cfv
    cmul
    co
    cmin
    co
    wceq
    recld.1
    cA
    remim
    syl
end
