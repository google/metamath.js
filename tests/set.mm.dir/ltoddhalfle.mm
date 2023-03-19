include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "wb.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "odd2np1.mm"
include "wa.mm"
include "cr.mm"
include "w3a.mm"
include "halfre.mm"
include "a1i.mm"
include "1red.mm"
include "zre.mm"
include "3jca.mm"
include "adantr.mm"
include "halflt1.mm"
include "axltadd.mm"
include "mpisyl.mm"
include "adantl.mm"
include "readdcld.mm"
include "peano2z.mm"
include "zred.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "zleltp1.mm"
include "ancoms.mm"
include "sylibrd.mm"
include "cc0.mm"
include "halfgt0.mm"
include "jca.mm"
include "ltaddpos.mm"
include "syl.mm"
include "mpbii.mm"
include "lelttr.mm"
include "impbid.mm"
include "cc.mm"
include "wne.mm"
include "zcn.mm"
include "1cnd.mm"
include "2cnne0.mm"
include "muldivdir.mm"
include "breq2d.mm"
include "2z.mm"
include "id.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "pncan1.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "3bitr4d.mm"
include "oveq1.mm"
include "bibi12d.mm"
include "syl5ibcom.mm"
include "ex.mm"
include "com23.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "3imp.mm"

theorem ltoddhalfle
  let cM: class M
  let cN: class N
  let vn: setvar n


  assert |- ( ( N e. ZZ /\ -. 2 || N /\ M e. ZZ ) -> ( M < ( N / 2 ) <-> M <_ ( ( N - 1 ) / 2 ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    cM
    cz
    wcel
    #
    cM
    cN
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cM
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    wb
    #
    @0
    @1
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    @2
    @8
    wi
    #
    vn
    cN
    odd2np1
    @0
    @12
    @13
    vn
    cz
    @0
    @9
    cz
    wcel
    #
    wa
    @2
    @12
    @8
    @14
    @2
    @12
    @8
    wi
    #
    wi
    @0
    @14
    @2
    @15
    @14
    @2
    wa
    #
    cM
    @11
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cM
    @11
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    wb
    @12
    @8
    @16
    cM
    @9
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    cM
    @9
    cle
    wbr
    #
    @18
    @21
    @16
    @24
    @25
    @16
    @24
    cM
    @9
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @25
    @16
    @24
    @23
    @26
    clt
    wbr
    #
    @27
    @16
    @22
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    w3a
    #
    @22
    c1
    clt
    wbr
    @28
    @14
    @32
    @2
    @14
    @29
    @30
    @31
    @29
    @14
    halfre
    a1i
    #
    @14
    1red
    @9
    zre
    #
    3jca
    adantr
    halflt1
    @22
    c1
    @9
    axltadd
    mpisyl
    @16
    cM
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    @26
    cr
    wcel
    #
    @24
    @28
    wa
    @27
    wi
    @2
    @35
    @14
    cM
    zre
    adantl
    #
    @14
    @36
    @2
    @14
    @9
    @22
    @34
    @33
    readdcld
    adantr
    #
    @14
    @37
    @2
    @14
    @26
    @9
    peano2z
    zred
    adantr
    cM
    @23
    @26
    lttr
    syl3anc
    mpan2d
    @2
    @14
    @25
    @27
    wb
    cM
    @9
    zleltp1
    ancoms
    sylibrd
    @16
    @25
    @9
    @23
    clt
    wbr
    #
    @24
    @16
    cc0
    @22
    clt
    wbr
    #
    @40
    halfgt0
    @16
    @29
    @31
    wa
    #
    @41
    @40
    wb
    @14
    @42
    @2
    @14
    @29
    @31
    @33
    @34
    jca
    adantr
    @22
    @9
    ltaddpos
    syl
    mpbii
    @16
    @35
    @31
    @36
    @25
    @40
    wa
    @24
    wi
    @38
    @14
    @31
    @2
    @34
    adantr
    @39
    cM
    @9
    @23
    lelttr
    syl3anc
    mpan2d
    impbid
    @14
    @18
    @24
    wb
    @2
    @14
    @17
    @23
    cM
    clt
    @14
    @9
    cc
    wcel
    c1
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    wa
    #
    @17
    @23
    wceq
    @9
    zcn
    #
    @14
    1cnd
    @44
    @14
    2cnne0
    a1i
    @9
    c1
    c2
    muldivdir
    syl3anc
    breq2d
    adantr
    @16
    @20
    @9
    cM
    cle
    @16
    @20
    @10
    c2
    cdiv
    co
    #
    @9
    @16
    @19
    @10
    c2
    cdiv
    @16
    @10
    cc
    wcel
    #
    @19
    @10
    wceq
    @14
    @47
    @2
    @14
    @10
    @14
    c2
    @9
    c2
    cz
    wcel
    @14
    2z
    a1i
    @14
    id
    zmulcld
    zcnd
    adantr
    @10
    pncan1
    syl
    oveq1d
    @14
    @46
    @9
    wceq
    @2
    @14
    @9
    c2
    @45
    @14
    2cnd
    @43
    @14
    2ne0
    a1i
    divcan3d
    adantr
    eqtrd
    breq2d
    3bitr4d
    @12
    @18
    @4
    @21
    @7
    @12
    @17
    @3
    cM
    clt
    @11
    cN
    c2
    cdiv
    oveq1
    breq2d
    @12
    @20
    @6
    cM
    cle
    @12
    @19
    @5
    c2
    cdiv
    @11
    cN
    c1
    cmin
    oveq1
    oveq1d
    breq2d
    bibi12d
    syl5ibcom
    ex
    adantl
    com23
    rexlimdva
    sylbid
    3imp
end
