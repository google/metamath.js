include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cre.mm"
include "wceq.mm"
include "recj.mm"
include "syl.mm"

theorem recjd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Re ` ( * ` A ) ) = ( Re ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cre
    cfv
    cA
    cre
    cfv
    wceq
    recld.1
    cA
    recj
    syl
end
