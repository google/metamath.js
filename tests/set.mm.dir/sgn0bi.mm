include "cxr.mm"
include "wcel.mm"
include "csgn.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "c1.mm"
include "cneg.mm"
include "id.mm"
include "eqeq1.mm"
include "bibi1d.mm"
include "wa.mm"
include "simpr.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "neneqd.mm"
include "gt0ne0d.mm"
include "2falsed.mm"
include "1cnd.mm"
include "negne0d.mm"
include "lt0ne0d.mm"
include "sgn3da.mm"

theorem sgn0bi
  let cA: class A


  assert |- ( A e. RR* -> ( ( sgn ` A ) = 0 <-> A = 0 ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    csgn
    cfv
    #
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    wb
    cc0
    cc0
    wceq
    #
    @3
    wb
    c1
    cc0
    wceq
    #
    @3
    wb
    c1
    cneg
    #
    cc0
    wceq
    #
    @3
    wb
    cA
    @0
    id
    @2
    @2
    @4
    @3
    @1
    cc0
    cc0
    eqeq1
    bibi1d
    @1
    c1
    wceq
    @2
    @5
    @3
    @1
    c1
    cc0
    eqeq1
    bibi1d
    @1
    @6
    wceq
    @2
    @7
    @3
    @1
    @6
    cc0
    eqeq1
    bibi1d
    @0
    @3
    wa
    #
    cc0
    cA
    cc0
    @8
    cA
    cc0
    @0
    @3
    simpr
    eqcomd
    eqeq1d
    @0
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @5
    @3
    @10
    c1
    cc0
    c1
    cc0
    wne
    #
    @10
    ax-1ne0
    a1i
    neneqd
    @10
    cA
    cc0
    @10
    cA
    @0
    @9
    simpr
    gt0ne0d
    neneqd
    2falsed
    @0
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    @7
    @3
    @13
    @6
    cc0
    @13
    c1
    @13
    1cnd
    @11
    @13
    ax-1ne0
    a1i
    negne0d
    neneqd
    @13
    cA
    cc0
    @13
    cA
    @0
    @12
    simpr
    lt0ne0d
    neneqd
    2falsed
    sgn3da
end
