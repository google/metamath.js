include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "sqrtmsq.mm"
include "syl2anc.mm"

theorem sqrtmsqd
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> ( sqrt ` ( A x. A ) ) = A )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    cA
    cmul
    co
    csqrt
    cfv
    cA
    wceq
    resqrcld.1
    resqrcld.2
    cA
    sqrtmsq
    syl2anc
end
