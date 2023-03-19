include "cxr.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cxmu.mm"
include "co.mm"
include "cxne.mm"
include "cr.mm"
include "wceq.mm"
include "1re.mm"
include "rexneg.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "rexri.mm"
include "xmulneg1.mm"
include "mpan.mm"
include "syl5eqr.mm"
include "xmulid2.mm"
include "xnegeq.mm"
include "syl.mm"
include "eqtrd.mm"

theorem xmulm1
  let cA: class A


  assert |- ( A e. RR* -> ( -u 1 *e A ) = -e A )

  proof
    cA
    cxr
    wcel
    #
    c1
    cneg
    #
    cA
    cxmu
    co
    #
    c1
    cA
    cxmu
    co
    #
    cxne
    #
    cA
    cxne
    #
    @0
    @2
    c1
    cxne
    #
    cA
    cxmu
    co
    #
    @4
    @6
    @1
    cA
    cxmu
    c1
    cr
    wcel
    @6
    @1
    wceq
    1re
    c1
    rexneg
    ax-mp
    oveq1i
    c1
    cxr
    wcel
    @0
    @7
    @4
    wceq
    c1
    1re
    rexri
    c1
    cA
    xmulneg1
    mpan
    syl5eqr
    @0
    @3
    cA
    wceq
    @4
    @5
    wceq
    cA
    xmulid2
    @3
    cA
    xnegeq
    syl
    eqtrd
end
