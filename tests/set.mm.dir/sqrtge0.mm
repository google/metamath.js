include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cre.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "resqrtthlem.mm"
include "simp2d.mm"
include "resqrtcl.mm"
include "rered.mm"
include "breqtrd.mm"

theorem sqrtge0
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> 0 <_ ( sqrt ` A ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    #
    cc0
    cA
    csqrt
    cfv
    #
    cre
    cfv
    #
    @1
    cle
    @0
    @1
    c2
    cexp
    co
    cA
    wceq
    cc0
    @2
    cle
    wbr
    ci
    @1
    cmul
    co
    crp
    wnel
    cA
    resqrtthlem
    simp2d
    @0
    @1
    cA
    resqrtcl
    rered
    breqtrd
end
