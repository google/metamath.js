include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "dvdszrcl.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "wrex.mm"
include "simpll.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "simpr.mm"
include "divcan2d.mm"
include "rspcedvd.mm"
include "w3a.mm"
include "3jca.mm"
include "dvdsval2.mm"
include "syl.mm"
include "mpbid.mm"
include "divides.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "exp31.mm"
include "com3r.mm"
include "mpd.mm"
include "imp.mm"

theorem divconjdvds
  let cM: class M
  let cN: class N
  let vm: setvar m


  assert |- ( ( M || N /\ M =/= 0 ) -> ( N / M ) || N )

  proof
    cM
    cN
    cdvds
    wbr
    #
    cM
    cc0
    wne
    #
    cN
    cM
    cdiv
    co
    #
    cN
    cdvds
    wbr
    #
    @0
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    @1
    @3
    wi
    cM
    cN
    dvdszrcl
    @6
    @1
    @0
    @3
    @6
    @1
    @0
    @3
    @6
    @1
    wa
    #
    @0
    wa
    #
    @3
    vm
    cv
    #
    @2
    cmul
    co
    #
    cN
    wceq
    #
    vm
    cz
    wrex
    #
    @7
    @12
    @0
    @7
    @11
    cM
    @2
    cmul
    co
    #
    cN
    wceq
    #
    vm
    cM
    cz
    @4
    @5
    @1
    simpll
    #
    @9
    cM
    wceq
    #
    @11
    @14
    wb
    @7
    @16
    @10
    @13
    cN
    @9
    cM
    @2
    cmul
    oveq1
    eqeq1d
    adantl
    @7
    cN
    cM
    @6
    cN
    cc
    wcel
    #
    @1
    @5
    @17
    @4
    cN
    zcn
    adantl
    adantr
    @6
    cM
    cc
    wcel
    #
    @1
    @4
    @18
    @5
    cM
    zcn
    adantr
    adantr
    @6
    @1
    simpr
    #
    divcan2d
    rspcedvd
    adantr
    @8
    @2
    cz
    wcel
    #
    @5
    @3
    @12
    wb
    @8
    @0
    @20
    @7
    @0
    simpr
    @8
    @4
    @1
    @5
    w3a
    #
    @0
    @20
    wb
    @7
    @21
    @0
    @7
    @4
    @1
    @5
    @15
    @19
    @6
    @5
    @1
    @4
    @5
    simpr
    adantr
    #
    3jca
    adantr
    cM
    cN
    dvdsval2
    syl
    mpbid
    @7
    @5
    @0
    @22
    adantr
    vm
    @2
    cN
    divides
    syl2anc
    mpbird
    exp31
    com3r
    mpd
    imp
end
