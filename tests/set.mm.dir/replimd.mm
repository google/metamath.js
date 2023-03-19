include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "replim.mm"
include "syl.mm"

theorem replimd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> A = ( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cA
    cre
    cfv
    ci
    cA
    cim
    cfv
    cmul
    co
    caddc
    co
    wceq
    recld.1
    cA
    replim
    syl
end
