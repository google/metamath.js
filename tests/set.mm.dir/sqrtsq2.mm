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
include "wb.mm"
include "resqrtcl.mm"
include "sqrtge0.mm"
include "jca.mm"
include "sq11.mm"
include "sylan.mm"
include "resqrtth.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "bitr3d.mm"

theorem sqrtsq2
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( sqrt ` A ) = B <-> A = ( B ^ 2 ) ) )

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
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    wa
    #
    wa
    #
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    wceq
    #
    @3
    cB
    wceq
    #
    cA
    @5
    wceq
    @0
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    @1
    @6
    @7
    wb
    @0
    @8
    @9
    cA
    resqrtcl
    cA
    sqrtge0
    jca
    @3
    cB
    sq11
    sylan
    @2
    @4
    cA
    @5
    @0
    @4
    cA
    wceq
    @1
    cA
    resqrtth
    adantr
    eqeq1d
    bitr3d
end
