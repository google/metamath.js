include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cdiv.mm"
include "wb.mm"
include "divides.mm"
include "3adant2.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "divmul3d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimprd.mm"
include "impr.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "rexlimdvaa.mm"
include "simpr.mm"
include "simp2.mm"
include "divcan1d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"

theorem dvdsval2
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( ( M e. ZZ /\ M =/= 0 /\ N e. ZZ ) -> ( M || N <-> ( N / M ) e. ZZ ) )

  proof
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cM
    cN
    cdvds
    wbr
    #
    vk
    cv
    #
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    cN
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    @2
    @4
    @8
    wb
    @1
    vk
    cM
    cN
    divides
    3adant2
    @3
    @8
    @10
    @3
    @7
    @10
    vk
    cz
    @3
    @5
    cz
    wcel
    #
    @7
    wa
    wa
    @9
    @5
    cz
    @3
    @11
    @7
    @9
    @5
    wceq
    #
    @3
    @11
    wa
    #
    @12
    @7
    @13
    @12
    cN
    @6
    wceq
    @7
    @13
    cN
    @5
    cM
    @3
    cN
    cc
    wcel
    #
    @11
    @2
    @0
    @14
    @1
    cN
    zcn
    3ad2ant3
    #
    adantr
    @11
    @5
    cc
    wcel
    @3
    @5
    zcn
    adantl
    @3
    cM
    cc
    wcel
    #
    @11
    @0
    @1
    @16
    @2
    cM
    zcn
    3ad2ant1
    #
    adantr
    @0
    @1
    @2
    @11
    simpl2
    divmul3d
    cN
    @6
    eqcom
    syl6bb
    biimprd
    impr
    @3
    @11
    @7
    simprl
    eqeltrd
    rexlimdvaa
    @3
    @10
    @8
    @3
    @10
    wa
    @10
    @9
    cM
    cmul
    co
    #
    cN
    wceq
    #
    @8
    @3
    @10
    simpr
    @3
    @19
    @10
    @3
    cN
    cM
    @15
    @17
    @0
    @1
    @2
    simp2
    divcan1d
    adantr
    @7
    @19
    vk
    @9
    cz
    @5
    @9
    wceq
    @6
    @18
    cN
    @5
    @9
    cM
    cmul
    oveq1
    eqeq1d
    rspcev
    syl2anc
    ex
    impbid
    bitrd
end
