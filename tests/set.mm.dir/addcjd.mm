include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cre.mm"
include "cmul.mm"
include "wceq.mm"
include "addcj.mm"
include "syl.mm"

theorem addcjd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A + ( * ` A ) ) = ( 2 x. ( Re ` A ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cA
    ccj
    cfv
    caddc
    co
    c2
    cA
    cre
    cfv
    cmul
    co
    wceq
    recld.1
    cA
    addcj
    syl
end
