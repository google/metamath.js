include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "wceq.mm"
include "absre.mm"
include "syl.mm"

theorem absred
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( abs ` A ) = ( sqrt ` ( A ^ 2 ) ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cabs
    cfv
    cA
    c2
    cexp
    co
    csqrt
    cfv
    wceq
    resqrcld.1
    cA
    absre
    syl
end
