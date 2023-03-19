include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "sqrtsq.mm"
include "syl2anc.mm"

theorem sqrtsqd
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> ( sqrt ` ( A ^ 2 ) ) = A )

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
    c2
    cexp
    co
    csqrt
    cfv
    cA
    wceq
    resqrcld.1
    resqrcld.2
    cA
    sqrtsq
    syl2anc
end
