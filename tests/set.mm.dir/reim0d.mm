include "cr.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "reim0.mm"
include "syl.mm"

theorem reim0d
  let wph: wff ph
  let cA: class A
  assume crred.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( Im ` A ) = 0 )

  proof
    wph
    cA
    cr
    wcel
    cA
    cim
    cfv
    cc0
    wceq
    crred.1
    cA
    reim0
    syl
end
