include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "clogb.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "logbval.mm"
include "wne.mm"
include "eldifsn.mm"
include "logcl.mm"
include "sylbi.mm"
include "adantl.mm"
include "eldifi.mm"
include "eldifpr.mm"
include "simp2bi.mm"
include "logcld.mm"
include "adantr.mm"
include "w3a.mm"
include "logccne0.mm"
include "divcld.mm"
include "eqeltrd.mm"

theorem logbcl
  let cB: class B
  let cX: class X


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) ) -> ( B logb X ) e. CC )

  proof
    cB
    cc
    cc0
    c1
    cpr
    #
    cdif
    wcel
    #
    cX
    cc
    cc0
    csn
    cdif
    wcel
    #
    wa
    #
    cB
    cX
    clogb
    co
    cX
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    cc
    cB
    cX
    logbval
    @3
    @4
    @5
    @2
    @4
    cc
    wcel
    #
    @1
    @2
    cX
    cc
    wcel
    cX
    cc0
    wne
    wa
    @6
    cX
    cc
    cc0
    eldifsn
    cX
    logcl
    sylbi
    adantl
    @1
    @5
    cc
    wcel
    @2
    @1
    cB
    cB
    cc
    @0
    eldifi
    @1
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
    cB
    cc
    cc0
    c1
    eldifpr
    #
    simp2bi
    logcld
    adantr
    @1
    @5
    cc0
    wne
    #
    @2
    @1
    @7
    @8
    @9
    w3a
    @11
    @10
    cB
    logccne0
    sylbi
    adantr
    divcld
    eqeltrd
end
