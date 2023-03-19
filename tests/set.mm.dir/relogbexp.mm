include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "clogb.mm"
include "cmul.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "3jca.mm"
include "eldifpr.mm"
include "sylibr.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp3.mm"
include "relogbzexp.mm"
include "syl3anc.mm"
include "logbid1.mm"
include "syl.mm"
include "oveq2d.mm"
include "zcn.mm"
include "3ad2ant3.mm"
include "mulid1d.mm"
include "3eqtrd.mm"

theorem relogbexp
  let cB: class B
  let cM: class M


  assert |- ( ( B e. RR+ /\ B =/= 1 /\ M e. ZZ ) -> ( B logb ( B ^ M ) ) = M )

  proof
    cB
    crp
    wcel
    #
    cB
    c1
    wne
    #
    cM
    cz
    wcel
    #
    w3a
    #
    cB
    cB
    cM
    cexp
    co
    clogb
    co
    #
    cM
    cB
    cB
    clogb
    co
    #
    cmul
    co
    #
    cM
    c1
    cmul
    co
    cM
    @3
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    @0
    @2
    @4
    @6
    wceq
    @0
    @1
    @7
    @2
    @0
    @1
    wa
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @1
    w3a
    #
    @7
    @8
    @9
    @10
    @1
    @0
    @9
    @1
    cB
    rpcn
    adantr
    @0
    @10
    @1
    cB
    rpne0
    adantr
    @0
    @1
    simpr
    3jca
    #
    cB
    cc
    cc0
    c1
    eldifpr
    sylibr
    3adant3
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    cB
    cB
    cM
    relogbzexp
    syl3anc
    @3
    @5
    c1
    cM
    cmul
    @3
    @11
    @5
    c1
    wceq
    @0
    @1
    @11
    @2
    @12
    3adant3
    cB
    logbid1
    syl
    oveq2d
    @3
    cM
    @2
    @0
    cM
    cc
    wcel
    @1
    cM
    zcn
    3ad2ant3
    mulid1d
    3eqtrd
end
