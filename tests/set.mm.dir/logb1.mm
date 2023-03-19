include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "clogb.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cpr.mm"
include "cdif.mm"
include "wceq.mm"
include "eldifpr.mm"
include "csn.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "logbval.mm"
include "mpan2.mm"
include "sylbir.mm"
include "log1.mm"
include "oveq1i.mm"
include "simp1.mm"
include "simp2.mm"
include "logcld.mm"
include "logccne0.mm"
include "div0d.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem logb1
  let cB: class B


  assert |- ( ( B e. CC /\ B =/= 0 /\ B =/= 1 ) -> ( B logb 1 ) = 0 )

  proof
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    #
    cB
    c1
    clogb
    co
    #
    c1
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cc0
    @3
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    @4
    @7
    wceq
    #
    cB
    cc
    cc0
    c1
    eldifpr
    @8
    c1
    cc
    cc0
    csn
    cdif
    wcel
    #
    @9
    @10
    c1
    cc
    wcel
    c1
    cc0
    wne
    ax-1cn
    ax-1ne0
    c1
    cc
    cc0
    eldifsn
    mpbir2an
    cB
    c1
    logbval
    mpan2
    sylbir
    @3
    @7
    cc0
    @6
    cdiv
    co
    cc0
    @5
    cc0
    @6
    cdiv
    log1
    oveq1i
    @3
    @6
    @3
    cB
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    logcld
    cB
    logccne0
    div0d
    syl5eq
    eqtrd
end
