include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csp.mm"
include "csqrt.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "normval.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "hiidge0.mm"
include "cr.mm"
include "hiidrcl.mm"
include "sqsqrti.mm"
include "eqtri.mm"

theorem normsqi
  let cA: class A
  assume normcl.1: |- A e. ~H


  assert |- ( ( normh ` A ) ^ 2 ) = ( A .ih A )

  proof
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    cA
    cA
    csp
    co
    #
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    @1
    @0
    @2
    c2
    cexp
    cA
    chil
    wcel
    #
    @0
    @2
    wceq
    normcl.1
    cA
    normval
    ax-mp
    oveq1i
    cc0
    @1
    cle
    wbr
    #
    @3
    @1
    wceq
    @4
    @5
    normcl.1
    cA
    hiidge0
    ax-mp
    @1
    @4
    @1
    cr
    wcel
    normcl.1
    cA
    hiidrcl
    ax-mp
    sqsqrti
    ax-mp
    eqtri
end
