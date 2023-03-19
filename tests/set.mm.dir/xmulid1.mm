include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "c1.mm"
include "cxmu.mm"
include "co.mm"
include "elxr.mm"
include "cmul.mm"
include "1re.mm"
include "rexmul.mm"
include "mpan2.mm"
include "ax-1rid.mm"
include "eqtrd.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rexri.mm"
include "0lt1.mm"
include "xmulpnf2.mm"
include "mp2an.mm"
include "oveq1.mm"
include "id.mm"
include "3eqtr4a.mm"
include "xmulmnf2.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem xmulid1
  let cA: class A


  assert |- ( A e. RR* -> ( A *e 1 ) = A )

  proof
    cA
    cxr
    wcel
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cA
    c1
    cxmu
    co
    #
    cA
    wceq
    #
    cA
    elxr
    @0
    @4
    @1
    @2
    @0
    @3
    cA
    c1
    cmul
    co
    #
    cA
    @0
    c1
    cr
    wcel
    @3
    @5
    wceq
    1re
    cA
    c1
    rexmul
    mpan2
    cA
    ax-1rid
    eqtrd
    @1
    cpnf
    c1
    cxmu
    co
    #
    cpnf
    @3
    cA
    c1
    cxr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    @6
    cpnf
    wceq
    c1
    1re
    rexri
    #
    0lt1
    c1
    xmulpnf2
    mp2an
    cA
    cpnf
    c1
    cxmu
    oveq1
    @1
    id
    3eqtr4a
    @2
    cmnf
    c1
    cxmu
    co
    #
    cmnf
    @3
    cA
    @7
    @8
    @10
    cmnf
    wceq
    @9
    0lt1
    c1
    xmulmnf2
    mp2an
    cA
    cmnf
    c1
    cxmu
    oveq1
    @2
    id
    3eqtr4a
    3jaoi
    sylbi
end
