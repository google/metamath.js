include "cr.mm"
include "wcel.mm"
include "cceil.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ceilge.mm"
include "syl.mm"

theorem ceilged
  let wph: wff ph
  let cA: class A
  assume ceilged.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A <_ ( |^ ` A ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cA
    cceil
    cfv
    cle
    wbr
    ceilged.1
    cA
    ceilge
    syl
end
