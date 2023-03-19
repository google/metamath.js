include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "w3a.mm"
include "clogb.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cr.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "simp1.mm"
include "rpcnne0d.mm"
include "simp3.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "eldifpr.mm"
include "sylibr.mm"
include "simp2.mm"
include "eldifsn.mm"
include "logbval.mm"
include "syl2anc.mm"
include "relogcl.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "logne0.mm"
include "3adant2.mm"
include "redivcld.mm"
include "eqeltrd.mm"

theorem relogbcl
  let cB: class B
  let cX: class X


  assert |- ( ( B e. RR+ /\ X e. RR+ /\ B =/= 1 ) -> ( B logb X ) e. RR )

  proof
    cB
    crp
    wcel
    #
    cX
    crp
    wcel
    #
    cB
    c1
    wne
    #
    w3a
    #
    cB
    cX
    clogb
    co
    #
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
    #
    cr
    @3
    cB
    cc
    cc0
    c1
    cpr
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
    @4
    @7
    wceq
    @3
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @2
    w3a
    #
    @8
    @3
    @10
    @11
    wa
    @2
    @12
    @3
    cB
    @0
    @1
    @2
    simp1
    rpcnne0d
    @0
    @1
    @2
    simp3
    @10
    @11
    @2
    df-3an
    sylanbrc
    cB
    cc
    cc0
    c1
    eldifpr
    sylibr
    @3
    cX
    cc
    wcel
    cX
    cc0
    wne
    wa
    @9
    @3
    cX
    @0
    @1
    @2
    simp2
    rpcnne0d
    cX
    cc
    cc0
    eldifsn
    sylibr
    cB
    cX
    logbval
    syl2anc
    @3
    @5
    @6
    @1
    @0
    @5
    cr
    wcel
    @2
    cX
    relogcl
    3ad2ant2
    @0
    @1
    @6
    cr
    wcel
    @2
    cB
    relogcl
    3ad2ant1
    @0
    @2
    @6
    cc0
    wne
    @1
    cB
    logne0
    3adant2
    redivcld
    eqeltrd
end
