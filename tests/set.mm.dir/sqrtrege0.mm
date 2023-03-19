include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "sqrtthlem.mm"
include "simp2d.mm"

theorem sqrtrege0
  let cA: class A


  assert |- ( A e. CC -> 0 <_ ( Re ` ( sqrt ` A ) ) )

  proof
    cA
    cc
    wcel
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
    sqrtthlem
    simp2d
end
