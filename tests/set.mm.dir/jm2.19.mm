include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "crmy.mm"
include "co.mm"
include "wb.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "rmyeq0.mm"
include "3adant2.mm"
include "0dvds.mm"
include "3ad2ant3.mm"
include "frmy.mm"
include "fovcl.mm"
include "syl.mm"
include "3bitr4d.mm"
include "adantr.mm"
include "simpr.mm"
include "breq1d.mm"
include "oveq2d.mm"
include "simpl1.mm"
include "rmy0.mm"
include "eqtrd.mm"
include "wne.mm"
include "cabs.mm"
include "cmo.mm"
include "wi.mm"
include "3adant3.mm"
include "dvds0.mm"
include "3ad2ant1.mm"
include "breqtrrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "ad2antrr.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "simplr.mm"
include "absrpcld.mm"
include "modlt.mm"
include "syl2anc.mm"
include "cn0.mm"
include "simpll1.mm"
include "simpll3.mm"
include "cn.mm"
include "simpll2.mm"
include "nnabscl.mm"
include "zmodcld.mm"
include "nn0abscl.mm"
include "ltrmynn0.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "nn0zd.mm"
include "rmyabs.mm"
include "modcld.mm"
include "modge0.mm"
include "absidd.mm"
include "3brtr4d.mm"
include "nn0red.mm"
include "ltnled.mm"
include "necon3bid.mm"
include "dvdsleabs2.mm"
include "mtod.mm"
include "ex.mm"
include "necon4ad.mm"
include "impbid.mm"
include "simpl2.mm"
include "simpl3.mm"
include "dvdsabsmod0.mm"
include "cmin.mm"
include "cdiv.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "modabsdifz.mm"
include "znegcld.mm"
include "jm2.19lem4.mm"
include "syl121anc.mm"
include "recnd.mm"
include "subcld.mm"
include "divcld.mm"
include "mulneg1d.mm"
include "mulcld.mm"
include "negsubd.mm"
include "divcan1d.mm"
include "nncand.mm"
include "3eqtrrd.mm"
include "bitr4d.mm"
include "pm2.61dane.mm"

theorem jm2.19
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M || N <-> ( A rmY M ) || ( A rmY N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
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
    cA
    cM
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    cdvds
    wbr
    #
    wb
    cM
    cc0
    @4
    cM
    cc0
    wceq
    #
    wa
    #
    cc0
    cN
    cdvds
    wbr
    #
    cc0
    @7
    cdvds
    wbr
    #
    @5
    @8
    @4
    @11
    @12
    wb
    @9
    @4
    cN
    cc0
    wceq
    #
    @7
    cc0
    wceq
    #
    @11
    @12
    @1
    @3
    @13
    @14
    wb
    @2
    cA
    cN
    rmyeq0
    3adant2
    @3
    @1
    @11
    @13
    wb
    @2
    cN
    0dvds
    3ad2ant3
    @4
    @7
    cz
    wcel
    #
    @12
    @14
    wb
    @1
    @3
    @15
    @2
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    3adant2
    @7
    0dvds
    syl
    3bitr4d
    adantr
    @10
    cM
    cc0
    cN
    cdvds
    @4
    @9
    simpr
    #
    breq1d
    @10
    @6
    cc0
    @7
    cdvds
    @10
    @6
    cA
    cc0
    crmy
    co
    #
    cc0
    @10
    cM
    cc0
    cA
    crmy
    @16
    oveq2d
    @10
    @1
    @17
    cc0
    wceq
    #
    @1
    @2
    @3
    @9
    simpl1
    cA
    rmy0
    #
    syl
    eqtrd
    breq1d
    3bitr4d
    @4
    cM
    cc0
    wne
    #
    wa
    #
    cN
    cM
    cabs
    cfv
    #
    cmo
    co
    #
    cc0
    wceq
    #
    @6
    cA
    @23
    crmy
    co
    #
    cdvds
    wbr
    #
    @5
    @8
    @21
    @24
    @26
    @4
    @24
    @26
    wi
    @20
    @4
    @26
    @24
    @6
    @17
    cdvds
    wbr
    @4
    @6
    cc0
    @17
    cdvds
    @4
    @6
    cz
    wcel
    #
    @6
    cc0
    cdvds
    wbr
    @1
    @2
    @27
    @3
    cA
    cM
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    3adant3
    #
    @6
    dvds0
    syl
    @1
    @2
    @18
    @3
    @19
    3ad2ant1
    breqtrrd
    @24
    @25
    @17
    @6
    cdvds
    @23
    cc0
    cA
    crmy
    oveq2
    breq2d
    syl5ibrcom
    adantr
    @21
    @26
    @23
    cc0
    @21
    @23
    cc0
    wne
    #
    @26
    wn
    @21
    @29
    wa
    #
    @26
    @6
    cabs
    cfv
    #
    @25
    cabs
    cfv
    #
    cle
    wbr
    #
    @30
    @32
    @31
    clt
    wbr
    @33
    wn
    @30
    @25
    cA
    @22
    crmy
    co
    #
    @32
    @31
    clt
    @30
    @23
    @22
    clt
    wbr
    #
    @25
    @34
    clt
    wbr
    #
    @30
    cN
    cr
    wcel
    #
    @22
    crp
    wcel
    #
    @35
    @4
    @37
    @20
    @29
    @3
    @1
    @37
    @2
    cN
    zre
    3ad2ant3
    #
    ad2antrr
    #
    @30
    cM
    @4
    cM
    cc
    wcel
    #
    @20
    @29
    @2
    @1
    @41
    @3
    cM
    zcn
    3ad2ant2
    #
    ad2antrr
    @4
    @20
    @29
    simplr
    #
    absrpcld
    #
    cN
    @22
    modlt
    syl2anc
    @30
    @1
    @23
    cn0
    wcel
    @22
    cn0
    wcel
    #
    @35
    @36
    wb
    @1
    @2
    @3
    @20
    @29
    simpll1
    #
    @30
    cN
    @22
    @1
    @2
    @3
    @20
    @29
    simpll3
    @30
    @2
    @20
    @22
    cn
    wcel
    @1
    @2
    @3
    @20
    @29
    simpll2
    #
    @43
    cM
    nnabscl
    syl2anc
    zmodcld
    #
    @4
    @45
    @20
    @29
    @2
    @1
    @45
    @3
    cM
    nn0abscl
    3ad2ant2
    ad2antrr
    cA
    @23
    @22
    ltrmynn0
    syl3anc
    mpbid
    @30
    @32
    cA
    @23
    cabs
    cfv
    #
    crmy
    co
    #
    @25
    @30
    @1
    @23
    cz
    wcel
    #
    @32
    @50
    wceq
    @46
    @30
    @23
    @48
    nn0zd
    #
    cA
    @23
    rmyabs
    syl2anc
    @30
    @49
    @23
    cA
    crmy
    @30
    @23
    @30
    cN
    @22
    @40
    @44
    modcld
    @30
    @37
    @38
    cc0
    @23
    cle
    wbr
    @40
    @44
    cN
    @22
    modge0
    syl2anc
    absidd
    oveq2d
    eqtrd
    @30
    @1
    @2
    @31
    @34
    wceq
    @46
    @47
    cA
    cM
    rmyabs
    syl2anc
    3brtr4d
    @30
    @32
    @31
    @30
    @32
    @30
    @25
    cz
    wcel
    #
    @32
    cn0
    wcel
    @30
    @1
    @51
    @53
    @46
    @52
    cA
    @23
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    #
    @25
    nn0abscl
    syl
    nn0red
    @30
    @31
    @30
    @27
    @31
    cn0
    wcel
    @4
    @27
    @20
    @29
    @28
    ad2antrr
    #
    @6
    nn0abscl
    syl
    nn0red
    ltnled
    mpbid
    @30
    @27
    @53
    @25
    cc0
    wne
    #
    @26
    @33
    wi
    @55
    @54
    @30
    @29
    @56
    @21
    @29
    simpr
    @30
    @23
    cc0
    @25
    cc0
    @30
    @1
    @51
    @24
    @25
    cc0
    wceq
    wb
    @46
    @52
    cA
    @23
    rmyeq0
    syl2anc
    necon3bid
    mpbid
    @6
    @25
    dvdsleabs2
    syl3anc
    mtod
    ex
    necon4ad
    impbid
    @21
    @2
    @3
    @20
    @5
    @24
    wb
    @1
    @2
    @3
    @20
    simpl2
    #
    @1
    @2
    @3
    @20
    simpl3
    #
    @4
    @20
    simpr
    #
    cM
    cN
    dvdsabsmod0
    syl3anc
    @21
    @8
    @6
    cA
    cN
    cN
    @23
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cneg
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    @26
    @21
    @1
    @2
    @3
    @62
    cz
    wcel
    @8
    @66
    wb
    @1
    @2
    @3
    @20
    simpl1
    @57
    @58
    @21
    @61
    @21
    @37
    cM
    cr
    wcel
    #
    @20
    @61
    cz
    wcel
    @4
    @37
    @20
    @39
    adantr
    #
    @4
    @67
    @20
    @2
    @1
    @67
    @3
    cM
    zre
    3ad2ant2
    adantr
    @59
    cM
    cN
    modabsdifz
    syl3anc
    znegcld
    cA
    @62
    cM
    cN
    jm2.19lem4
    syl121anc
    @21
    @25
    @65
    @6
    cdvds
    @21
    @23
    @64
    cA
    crmy
    @21
    @64
    cN
    @61
    cM
    cmul
    co
    #
    cneg
    #
    caddc
    co
    cN
    @69
    cmin
    co
    #
    @23
    @21
    @63
    @70
    cN
    caddc
    @21
    @61
    cM
    @21
    @60
    cM
    @21
    cN
    @23
    @4
    cN
    cc
    wcel
    @20
    @4
    cN
    @39
    recnd
    adantr
    #
    @21
    @23
    @21
    cN
    @22
    @68
    @21
    cM
    @4
    @41
    @20
    @42
    adantr
    #
    @59
    absrpcld
    modcld
    recnd
    #
    subcld
    #
    @73
    @59
    divcld
    #
    @73
    mulneg1d
    oveq2d
    @21
    cN
    @69
    @72
    @21
    @61
    cM
    @76
    @73
    mulcld
    negsubd
    @21
    @71
    cN
    @60
    cmin
    co
    @23
    @21
    @69
    @60
    cN
    cmin
    @21
    @60
    cM
    @75
    @73
    @59
    divcan1d
    oveq2d
    @21
    cN
    @23
    @72
    @74
    nncand
    eqtrd
    3eqtrrd
    oveq2d
    breq2d
    bitr4d
    3bitr4d
    pm2.61dane
end
