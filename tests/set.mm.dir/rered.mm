include "cr.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "rere.mm"
include "syl.mm"

theorem rered
  let wph: wff ph
  let cA: class A
  assume crred.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( Re ` A ) = A )

  proof
    wph
    cA
    cr
    wcel
    cA
    cre
    cfv
    cA
    wceq
    crred.1
    cA
    rere
    syl
end
