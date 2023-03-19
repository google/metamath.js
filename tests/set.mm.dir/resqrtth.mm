include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "resqrtthlem.mm"
include "simp1d.mm"

theorem resqrtth
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( ( sqrt ` A ) ^ 2 ) = A )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    cA
    wceq
    cc0
    @0
    cre
    cfv
    cle
    wbr
    ci
    @0
    cmul
    co
    crp
    wnel
    cA
    resqrtthlem
    simp1d
end
