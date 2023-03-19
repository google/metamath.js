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
include "csn.mm"
include "wceq.mm"
include "eldifpr.mm"
include "biimpri.mm"
include "wa.mm"
include "eldifsn.mm"
include "3adant3.mm"
include "logbval.mm"
include "syl2anc.mm"
include "logcl.mm"
include "logccne0.mm"
include "dividd.mm"
include "eqtrd.mm"

theorem logbid1
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> ( A logb A ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    c1
    wne
    #
    w3a
    #
    cA
    cA
    clogb
    co
    #
    cA
    clog
    cfv
    #
    @5
    cdiv
    co
    #
    c1
    @3
    cA
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cA
    cc
    cc0
    csn
    cdif
    wcel
    #
    @4
    @6
    wceq
    @7
    @3
    cA
    cc
    cc0
    c1
    eldifpr
    biimpri
    @0
    @1
    @8
    @2
    @8
    @0
    @1
    wa
    cA
    cc
    cc0
    eldifsn
    biimpri
    3adant3
    cA
    cA
    logbval
    syl2anc
    @3
    @5
    @0
    @1
    @5
    cc
    wcel
    @2
    cA
    logcl
    3adant3
    cA
    logccne0
    dividd
    eqtrd
end
