include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "wb.mm"
include "resqcl.mm"
include "sqge0.mm"
include "jca.mm"
include "adantr.mm"
include "sqrtsq2.mm"
include "mpancom.mm"
include "mpbiri.mm"

theorem sqrtsq
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( sqrt ` ( A ^ 2 ) ) = A )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    csqrt
    cfv
    cA
    wceq
    #
    @3
    @3
    wceq
    #
    @3
    eqid
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
    #
    @2
    @4
    @5
    wb
    @0
    @8
    @1
    @0
    @6
    @7
    cA
    resqcl
    cA
    sqge0
    jca
    adantr
    @3
    cA
    sqrtsq2
    mpancom
    mpbiri
end
