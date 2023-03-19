include "cr.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjre.mm"
include "syl.mm"

theorem cjred
  let wph: wff ph
  let cA: class A
  assume crred.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( * ` A ) = A )

  proof
    wph
    cA
    cr
    wcel
    cA
    ccj
    cfv
    cA
    wceq
    crred.1
    cA
    cjre
    syl
end
