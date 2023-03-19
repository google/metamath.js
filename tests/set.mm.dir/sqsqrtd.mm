include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "sqrtth.mm"
include "syl.mm"

theorem sqsqrtd
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( sqrt ` A ) ^ 2 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    csqrt
    cfv
    c2
    cexp
    co
    cA
    wceq
    abscld.1
    cA
    sqrtth
    syl
end
