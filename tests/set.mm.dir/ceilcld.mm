include "cr.mm"
include "wcel.mm"
include "cceil.mm"
include "cfv.mm"
include "cz.mm"
include "ceilcl.mm"
include "syl.mm"

theorem ceilcld
  let wph: wff ph
  let cA: class A
  assume ceilcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( |^ ` A ) e. ZZ )

  proof
    wph
    cA
    cr
    wcel
    cA
    cceil
    cfv
    cz
    wcel
    ceilcld.1
    cA
    ceilcl
    syl
end
