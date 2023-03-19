include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cexp.mm"
include "wb.mm"
include "divides.mm"
include "3adant3.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl3.mm"
include "iddvdsexp.mm"
include "syl2anc.mm"
include "cn0.mm"
include "simpr.mm"
include "nnnn0.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "zexpcl.mm"
include "dvdsmul2.mm"
include "wi.mm"
include "zmulcld.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "mulexpd.mm"
include "breqtrrd.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"

theorem dvdspw
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. NN ) -> ( K || M -> K || ( M ^ N ) ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cK
    cM
    cdvds
    wbr
    #
    vm
    cv
    #
    cK
    cmul
    co
    #
    cM
    wceq
    #
    vm
    cz
    wrex
    #
    cK
    cM
    cN
    cexp
    co
    #
    cdvds
    wbr
    #
    @0
    @1
    @4
    @8
    wb
    @2
    vm
    cK
    cM
    divides
    3adant3
    @3
    @7
    @10
    vm
    cz
    @3
    @5
    cz
    wcel
    #
    wa
    #
    cK
    @6
    cN
    cexp
    co
    #
    cdvds
    wbr
    @7
    @10
    @12
    cK
    @5
    cN
    cexp
    co
    #
    cK
    cN
    cexp
    co
    #
    cmul
    co
    #
    @13
    cdvds
    @12
    cK
    @15
    cdvds
    wbr
    #
    @15
    @16
    cdvds
    wbr
    #
    cK
    @16
    cdvds
    wbr
    #
    @12
    @0
    @2
    @17
    @0
    @1
    @2
    @11
    simpl1
    #
    @0
    @1
    @2
    @11
    simpl3
    cK
    cN
    iddvdsexp
    syl2anc
    @12
    @14
    cz
    wcel
    #
    @15
    cz
    wcel
    #
    @18
    @12
    @11
    cN
    cn0
    wcel
    #
    @21
    @3
    @11
    simpr
    @3
    @23
    @11
    @2
    @0
    @23
    @1
    cN
    nnnn0
    3ad2ant3
    adantr
    #
    @5
    cN
    zexpcl
    syl2anc
    #
    @12
    @0
    @23
    @22
    @20
    @24
    cK
    cN
    zexpcl
    syl2anc
    #
    @14
    @15
    dvdsmul2
    syl2anc
    @12
    @0
    @22
    @16
    cz
    wcel
    @17
    @18
    wa
    @19
    wi
    @20
    @26
    @12
    @14
    @15
    @25
    @26
    zmulcld
    cK
    @15
    @16
    dvdstr
    syl3anc
    mp2and
    @12
    @5
    cK
    cN
    @11
    @5
    cc
    wcel
    @3
    @5
    zcn
    adantl
    @3
    cK
    cc
    wcel
    #
    @11
    @0
    @1
    @27
    @2
    cK
    zcn
    3ad2ant1
    adantr
    @24
    mulexpd
    breqtrrd
    @7
    @13
    @9
    cK
    cdvds
    @6
    cM
    cN
    cexp
    oveq1
    breq2d
    syl5ibcom
    rexlimdva
    sylbid
end
