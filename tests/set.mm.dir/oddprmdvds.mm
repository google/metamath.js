include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "wn.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cpc.mm"
include "cdiv.mm"
include "wi.mm"
include "2prm.mm"
include "pcndvds2.mm"
include "mpan.mm"
include "pcdvds.mm"
include "wa.mm"
include "wb.mm"
include "id.mm"
include "2nn.mm"
include "a1i.mm"
include "pccld.mm"
include "nnexpcld.mm"
include "jca.mm"
include "nndivdvds.mm"
include "syl.mm"
include "adantr.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "nncn.mm"
include "nnne0.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "diveq1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "simpr.mm"
include "rspcedvd.mm"
include "ex.mm"
include "pm2.24.mm"
include "syl6.mm"
include "sylbid.mm"
include "com12.mm"
include "exprmfct.mm"
include "breq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "cmul.mm"
include "prmnn.mm"
include "mpbid.mm"
include "nndivides.mm"
include "syl2anr.mm"
include "eqcom.mm"
include "nnmulcld.mm"
include "nncnd.mm"
include "3jca.mm"
include "divmul.mm"
include "syl5bb.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "cz.mm"
include "nnzd.mm"
include "dvdsmul2.mm"
include "2nn0.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "mulass.mm"
include "breqtrd.mm"
include "breq2.mm"
include "a1d.mm"
include "exp31.mm"
include "com23.mm"
include "rexlimdva.mm"
include "syldd.mm"
include "impd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "mp2d.mm"
include "imp.mm"

theorem oddprmdvds
  let vn: setvar n
  let cK: class K
  let vp: setvar p
  let vm: setvar m
  let vq: setvar q

  disjoint K n
  disjoint K p
  disjoint n p
  disjoint K m
  disjoint K q
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint n q
  disjoint p q
  assert |- ( ( K e. NN /\ -. E. n e. NN0 K = ( 2 ^ n ) ) -> E. p e. ( Prime \ { 2 } ) p || K )

  proof
    cK
    cn
    wcel
    #
    cK
    c2
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    wn
    #
    vp
    cv
    #
    cK
    cdvds
    wbr
    #
    vp
    cprime
    c2
    csn
    cdif
    #
    wrex
    #
    @0
    c2
    cK
    c2
    c2
    cK
    cpc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    wn
    #
    @11
    cK
    cdvds
    wbr
    #
    @5
    @9
    wi
    #
    c2
    cprime
    wcel
    #
    @0
    @14
    2prm
    c2
    cK
    pcndvds2
    mpan
    @17
    @0
    @15
    2prm
    c2
    cK
    pcdvds
    mpan
    #
    @0
    @14
    @15
    @16
    wi
    @0
    @14
    wa
    #
    @15
    @12
    cn
    wcel
    #
    @16
    @0
    @15
    @20
    wb
    #
    @14
    @0
    @0
    @11
    cn
    wcel
    #
    wa
    @21
    @0
    @0
    @22
    @0
    id
    #
    @0
    c2
    @10
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @0
    c2
    cK
    @17
    @0
    2prm
    a1i
    @23
    pccld
    #
    nnexpcld
    #
    jca
    cK
    @11
    nndivdvds
    syl
    #
    adantr
    @20
    @19
    @16
    @20
    @12
    c1
    wceq
    #
    @12
    c2
    cuz
    cfv
    wcel
    #
    wo
    @19
    @16
    wi
    #
    @12
    elnn1uz2
    @27
    @29
    @28
    @19
    @27
    @16
    @19
    @27
    cK
    @11
    wceq
    #
    @16
    @19
    cK
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @11
    cc0
    wne
    #
    w3a
    #
    @27
    @30
    wb
    @0
    @34
    @14
    @0
    @31
    @32
    @33
    wa
    #
    @34
    cK
    nncn
    #
    @0
    @22
    @35
    @25
    @22
    @32
    @33
    @11
    nncn
    @11
    nnne0
    jca
    #
    syl
    @31
    @32
    @33
    3anass
    sylanbrc
    adantr
    cK
    @11
    diveq1
    syl
    @0
    @30
    @16
    wi
    @14
    @0
    @30
    @4
    @16
    @0
    @30
    @4
    @0
    @30
    wa
    #
    @3
    @30
    vn
    @10
    cn0
    @0
    @10
    cn0
    wcel
    @30
    @24
    adantr
    @1
    @10
    wceq
    #
    @3
    @30
    wb
    @38
    @39
    @2
    @11
    cK
    @1
    @10
    c2
    cexp
    oveq2
    eqeq2d
    adantl
    @0
    @30
    simpr
    rspcedvd
    ex
    @4
    @9
    pm2.24
    syl6
    adantr
    sylbid
    com12
    @28
    vq
    cv
    #
    @12
    cdvds
    wbr
    #
    vq
    cprime
    wrex
    #
    @29
    @12
    vq
    exprmfct
    @42
    @0
    @14
    @16
    @0
    @42
    @14
    @16
    wi
    #
    @0
    @41
    @43
    vq
    cprime
    @0
    @40
    cprime
    wcel
    #
    wa
    #
    @41
    @14
    @40
    c2
    wne
    #
    @16
    @45
    @41
    @14
    @46
    wi
    @45
    @41
    wa
    @13
    @40
    c2
    @41
    @40
    c2
    wceq
    #
    @13
    wi
    @45
    @47
    @41
    @13
    @40
    c2
    @12
    cdvds
    breq1
    biimpcd
    adantl
    necon3bd
    ex
    @45
    @41
    vm
    cv
    #
    @40
    cmul
    co
    #
    @12
    wceq
    #
    vm
    cn
    wrex
    #
    @46
    @16
    wi
    #
    @44
    @40
    cn
    wcel
    #
    @20
    @41
    @51
    wb
    @0
    @40
    prmnn
    #
    @0
    @15
    @20
    @18
    @26
    mpbid
    vm
    @40
    @12
    nndivides
    syl2anr
    @45
    @50
    @52
    vm
    cn
    @45
    @48
    cn
    wcel
    #
    wa
    #
    @50
    @11
    @49
    cmul
    co
    #
    cK
    wceq
    #
    @52
    @50
    @12
    @49
    wceq
    #
    @56
    @58
    @49
    @12
    eqcom
    @56
    @31
    @49
    cc
    wcel
    #
    @35
    w3a
    @59
    @58
    wb
    @56
    @31
    @60
    @35
    @45
    @31
    @55
    @0
    @31
    @44
    @36
    adantr
    adantr
    @56
    @49
    @56
    @48
    @40
    @45
    @55
    simpr
    #
    @45
    @53
    @55
    @44
    @53
    @0
    @54
    adantl
    adantr
    nnmulcld
    nncnd
    @56
    @22
    @35
    @45
    @22
    @55
    @0
    @22
    @44
    @25
    adantr
    adantr
    #
    @37
    syl
    3jca
    cK
    @49
    @11
    divmul
    syl
    syl5bb
    @56
    @46
    @58
    @16
    @56
    @46
    @58
    @16
    @56
    @46
    wa
    #
    @58
    wa
    #
    @9
    @5
    @64
    @7
    @40
    cK
    cdvds
    wbr
    #
    vp
    @40
    @8
    @63
    @40
    @8
    wcel
    #
    @58
    @63
    @44
    @46
    wa
    @66
    @56
    @44
    @46
    @45
    @44
    @55
    @0
    @44
    simpr
    adantr
    anim1i
    @40
    cprime
    c2
    eldifsn
    sylibr
    adantr
    @6
    @40
    wceq
    @7
    @65
    wb
    @64
    @6
    @40
    cK
    cdvds
    breq1
    adantl
    @64
    @40
    @57
    cdvds
    wbr
    #
    @65
    @63
    @67
    @58
    @63
    @40
    @11
    @48
    cmul
    co
    #
    @40
    cmul
    co
    #
    @57
    cdvds
    @63
    @68
    cz
    wcel
    #
    @40
    cz
    wcel
    #
    wa
    #
    @40
    @69
    cdvds
    wbr
    @56
    @72
    @46
    @56
    @70
    @71
    @56
    @68
    @56
    @11
    @48
    @62
    @61
    nnmulcld
    nnzd
    @45
    @71
    @55
    @44
    @71
    @0
    @44
    @40
    @54
    nnzd
    adantl
    adantr
    jca
    adantr
    @68
    @40
    dvdsmul2
    syl
    @63
    @32
    @48
    cc
    wcel
    #
    @40
    cc
    wcel
    #
    w3a
    #
    @69
    @57
    wceq
    @56
    @75
    @46
    @56
    @32
    @73
    @74
    @56
    @11
    @45
    @11
    cn0
    wcel
    #
    @55
    @0
    @76
    @44
    @0
    c2
    @10
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    @24
    nn0expcld
    adantr
    adantr
    nn0cnd
    @55
    @73
    @45
    @48
    nncn
    adantl
    @45
    @74
    @55
    @44
    @74
    @0
    @44
    @40
    @54
    nncnd
    adantl
    adantr
    3jca
    adantr
    @11
    @48
    @40
    mulass
    syl
    breqtrd
    adantr
    @58
    @67
    @65
    wb
    @63
    @57
    cK
    @40
    cdvds
    breq2
    adantl
    mpbid
    rspcedvd
    a1d
    exp31
    com23
    sylbid
    rexlimdva
    sylbid
    syldd
    rexlimdva
    com12
    impd
    syl
    jaoi
    sylbi
    com12
    sylbid
    ex
    mp2d
    imp
end
