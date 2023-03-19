include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "2nn.mm"
include "a1i.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmin.mm"
include "cmo.mm"
include "wceq.mm"
include "cdiv.mm"
include "cgcd.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "wi.mm"
include "cprime.mm"
include "wb.mm"
include "simpr.mm"
include "2prm.mm"
include "adantr.mm"
include "prmdvdsexpb.mm"
include "syl3anc.mm"
include "cneg.mm"
include "cc.mm"
include "clt.mm"
include "proththdlem.mm"
include "simp1d.mm"
include "peano2cnm.mm"
include "syl.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "zcn.mm"
include "adantl.mm"
include "cn0.mm"
include "2nn0.mm"
include "simp3d.mm"
include "expmuld.mm"
include "ad4ant13.mm"
include "anim1i.mm"
include "ancomd.mm"
include "zexpcl.mm"
include "crp.mm"
include "nnrpd.mm"
include "ad3antrrr.mm"
include "simp2d.mm"
include "modexp2m1d.mm"
include "cr.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "anim2i.mm"
include "ancoms.mm"
include "zred.mm"
include "1red.mm"
include "renegcld.mm"
include "eqcoms.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "eqidd.mm"
include "modsub12d.mm"
include "peano2zm.mm"
include "ad2antrr.mm"
include "modgcd.mm"
include "syl2anc.mm"
include "ax-1cn.mm"
include "negdi2.mm"
include "mp2an.mm"
include "1p1e2.mm"
include "negeqi.mm"
include "eqtri.mm"
include "nnnegz.mm"
include "2z.mm"
include "nnzd.mm"
include "neggcd.mm"
include "sylancr.mm"
include "w3a.mm"
include "wn.mm"
include "nnz.mm"
include "oddm1d2.mm"
include "biimprd.mm"
include "impel.mm"
include "isoddgcd1.mm"
include "mpbid.mm"
include "3adant2.mm"
include "3eqtr3d.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpid.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "pockthg.mm"

theorem proththd
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cK: class K
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  assume proththd.n: |- ( ph -> N e. NN )
  assume proththd.k: |- ( ph -> K e. NN )
  assume proththd.p: |- ( ph -> P = ( ( K x. ( 2 ^ N ) ) + 1 ) )
  assume proththd.l: |- ( ph -> K < ( 2 ^ N ) )
  assume proththd.x: |- ( ph -> E. x e. ZZ ( ( x ^ ( ( P - 1 ) / 2 ) ) mod P ) = ( -u 1 mod P ) )

  disjoint N x
  disjoint P x
  disjoint ph x
  disjoint N p
  disjoint p x
  disjoint P p
  disjoint p ph
  disjoint k x
  assert |- ( ph -> P e. Prime )

  proof
    wph
    vx
    c2
    cN
    cexp
    co
    #
    cK
    cP
    vp
    wph
    c2
    cN
    c2
    cn
    wcel
    #
    wph
    2nn
    a1i
    #
    wph
    cN
    proththd.n
    nnnn0d
    nnexpcld
    #
    proththd.k
    proththd.l
    wph
    cP
    cK
    @0
    cmul
    co
    #
    c1
    caddc
    co
    @0
    cK
    cmul
    co
    #
    c1
    caddc
    co
    proththd.p
    wph
    @4
    @5
    c1
    caddc
    wph
    cK
    @0
    wph
    cK
    proththd.k
    nncnd
    wph
    @0
    @3
    nncnd
    mulcomd
    oveq1d
    eqtrd
    wph
    vp
    cv
    #
    @0
    cdvds
    wbr
    #
    vx
    cv
    #
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    wceq
    #
    @8
    @9
    @6
    cdiv
    co
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cP
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    vx
    cz
    wrex
    #
    wi
    vp
    cprime
    wph
    @6
    cprime
    wcel
    #
    wa
    #
    @7
    @6
    c2
    wceq
    #
    @19
    @21
    @20
    c2
    cprime
    wcel
    #
    cN
    cn
    wcel
    #
    @7
    @22
    wb
    wph
    @20
    simpr
    @23
    @21
    2prm
    a1i
    wph
    @24
    @20
    proththd.n
    adantr
    @6
    c2
    cN
    prmdvdsexpb
    syl3anc
    wph
    @22
    @19
    wi
    @20
    wph
    @22
    @8
    @9
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    cneg
    #
    cP
    cmo
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    @19
    proththd.x
    wph
    @22
    @31
    @19
    wi
    wph
    @22
    wa
    #
    @30
    @18
    vx
    cz
    @32
    @8
    cz
    wcel
    #
    wa
    #
    @30
    @18
    @34
    @30
    wa
    #
    @12
    @17
    @35
    @11
    @26
    c2
    cexp
    co
    #
    cP
    cmo
    co
    c1
    @35
    @10
    @36
    cP
    cmo
    wph
    @33
    @10
    @36
    wceq
    @22
    @30
    wph
    @33
    wa
    #
    @10
    @8
    @25
    c2
    cmul
    co
    #
    cexp
    co
    @36
    @37
    @9
    @38
    @8
    cexp
    @37
    @38
    @9
    @37
    @9
    c2
    wph
    @9
    cc
    wcel
    #
    @33
    wph
    cP
    cc
    wcel
    @39
    wph
    cP
    wph
    cP
    cn
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @25
    cn
    wcel
    #
    wph
    cP
    cK
    cN
    proththd.n
    proththd.k
    proththd.p
    proththdlem
    #
    simp1d
    #
    nncnd
    cP
    peano2cnm
    syl
    adantr
    @37
    2cnd
    c2
    cc0
    wne
    @37
    2ne0
    a1i
    divcan1d
    eqcomd
    oveq2d
    @37
    @8
    @25
    c2
    @33
    @8
    cc
    wcel
    wph
    @8
    zcn
    adantl
    c2
    cn0
    wcel
    @37
    2nn0
    a1i
    wph
    @25
    cn0
    wcel
    #
    @33
    wph
    @25
    wph
    @40
    @41
    @42
    @43
    simp3d
    nnnn0d
    #
    adantr
    expmuld
    eqtrd
    ad4ant13
    oveq1d
    @35
    @26
    cP
    @34
    @26
    cz
    wcel
    #
    @30
    @34
    @33
    @45
    wa
    @47
    @34
    @45
    @33
    @32
    @45
    @33
    wph
    @45
    @22
    @46
    adantr
    #
    anim1i
    ancomd
    @8
    @25
    zexpcl
    syl
    adantr
    wph
    cP
    crp
    wcel
    @22
    @33
    @30
    wph
    cP
    @44
    nnrpd
    ad3antrrr
    #
    wph
    @41
    @22
    @33
    @30
    wph
    @40
    @41
    @42
    @43
    simp2d
    ad3antrrr
    @34
    @30
    simpr
    modexp2m1d
    eqtrd
    @35
    @15
    cP
    cmo
    co
    #
    cP
    cgcd
    co
    #
    @28
    c1
    cmin
    co
    #
    cP
    cmo
    co
    #
    cP
    cgcd
    co
    #
    @16
    c1
    @35
    @50
    @53
    cP
    cgcd
    @35
    @14
    @28
    c1
    c1
    cP
    @34
    @14
    cr
    wcel
    @30
    @34
    @14
    @34
    @33
    @13
    cn0
    wcel
    #
    wa
    #
    @14
    cz
    wcel
    #
    @33
    @32
    @56
    @32
    @55
    @33
    @32
    @55
    @45
    @48
    @22
    @55
    @45
    wb
    wph
    @22
    @13
    @25
    cn0
    @6
    c2
    @9
    cdiv
    oveq2
    eleq1d
    adantl
    mpbird
    anim2i
    ancoms
    @8
    @13
    zexpcl
    syl
    #
    zred
    adantr
    @35
    c1
    @35
    1red
    #
    renegcld
    @59
    @59
    @49
    @34
    @30
    @14
    cP
    cmo
    co
    #
    @29
    wceq
    #
    @32
    @30
    @61
    wb
    #
    @33
    @22
    @62
    wph
    @22
    @27
    @60
    @29
    @22
    @26
    @14
    cP
    cmo
    @22
    @25
    @13
    @8
    cexp
    @25
    @13
    wceq
    c2
    @6
    c2
    @6
    @9
    cdiv
    oveq2
    eqcoms
    oveq2d
    oveq1d
    eqeq1d
    adantl
    adantr
    biimpa
    @35
    c1
    cP
    cmo
    co
    eqidd
    modsub12d
    oveq1d
    @34
    @51
    @16
    wceq
    #
    @30
    @34
    @15
    cz
    wcel
    #
    @40
    @63
    @34
    @57
    @64
    @58
    @14
    peano2zm
    syl
    wph
    @40
    @22
    @33
    @44
    ad2antrr
    @15
    cP
    modgcd
    syl2anc
    adantr
    wph
    @54
    c1
    wceq
    @22
    @33
    @30
    wph
    @54
    c2
    cneg
    #
    cP
    cmo
    co
    #
    cP
    cgcd
    co
    #
    c1
    wph
    @53
    @66
    cP
    cgcd
    wph
    @52
    @65
    cP
    cmo
    @52
    @65
    wceq
    wph
    @52
    c1
    c1
    caddc
    co
    #
    cneg
    #
    @65
    c1
    cc
    wcel
    #
    @70
    @52
    @69
    wceq
    ax-1cn
    ax-1cn
    @70
    @70
    wa
    @69
    @52
    c1
    c1
    negdi2
    eqcomd
    mp2an
    @68
    c2
    1p1e2
    negeqi
    eqtri
    a1i
    oveq1d
    oveq1d
    wph
    @67
    @65
    cP
    cgcd
    co
    #
    c1
    wph
    @65
    cz
    wcel
    #
    @40
    @67
    @71
    wceq
    wph
    @1
    @72
    @2
    c2
    nnnegz
    syl
    @44
    @65
    cP
    modgcd
    syl2anc
    wph
    @71
    c2
    cP
    cgcd
    co
    #
    c1
    wph
    c2
    cz
    wcel
    cP
    cz
    wcel
    #
    @71
    @73
    wceq
    2z
    wph
    cP
    @44
    nnzd
    c2
    cP
    neggcd
    sylancr
    wph
    @40
    @41
    @42
    w3a
    @73
    c1
    wceq
    #
    @43
    @40
    @42
    @75
    @41
    @40
    @42
    wa
    c2
    cP
    cdvds
    wbr
    wn
    #
    @75
    @40
    @25
    cz
    wcel
    #
    @76
    @42
    @40
    @76
    @77
    @40
    @74
    @76
    @77
    wb
    cP
    nnz
    #
    cP
    oddm1d2
    syl
    biimprd
    @25
    nnz
    impel
    @40
    @76
    @75
    wb
    #
    @42
    @40
    @74
    @79
    @78
    cP
    isoddgcd1
    syl
    adantr
    mpbid
    3adant2
    syl
    eqtrd
    eqtrd
    eqtrd
    ad3antrrr
    3eqtr3d
    jca
    ex
    reximdva
    ex
    mpid
    adantr
    sylbid
    ralrimiva
    pockthg
end
