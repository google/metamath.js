include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjcj.mm"
include "syl.mm"

theorem cjcjd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( * ` ( * ` A ) ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccj
    cfv
    ccj
    cfv
    cA
    wceq
    recld.1
    cA
    cjcj
    syl
end
