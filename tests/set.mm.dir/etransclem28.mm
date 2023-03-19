include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "cdvds.mm"
include "wceq.mm"
include "wa.mm"
include "cneg.mm"
include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "faccld.mm"
include "nnzd.mm"
include "adantr.mm"
include "csu.mm"
include "cmap.mm"
include "crab.mm"
include "etransclem12.mm"
include "eleqtrd.mm"
include "fveq1.mm"
include "sumeq2ad.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "nfcv.mm"
include "fzfid.mm"
include "cvv.mm"
include "wss.mm"
include "nn0ex.mm"
include "fzssnn0.mm"
include "a1i.mm"
include "mapss.mm"
include "sylancr.mm"
include "elrabi.mm"
include "sseldd.mm"
include "mccl.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "df-neg.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "ifeq2d.mm"
include "prodeq2ad.mm"
include "adantl.mm"
include "wf.mm"
include "elmapi.mm"
include "etransclem7.mm"
include "zmulcld.mm"
include "3jca.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "dvdsmultr2.mm"
include "sylc.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "simplr.mm"
include "simpr.mm"
include "etransclem14.mm"
include "breqtrrd.mm"
include "wn.mm"
include "dvds0.mm"
include "wne.mm"
include "neqne.mm"
include "etransclem15.mm"
include "pm2.61dan.mm"
include "elfznn0.mm"
include "nn0zd.mm"
include "etransclem26.mm"
include "caddc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "facp1.mm"
include "3eqtrrd.mm"
include "cle.mm"
include "1zzd.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "nnge1d.mm"
include "elfzle2.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "etransclem25.mm"
include "eqbrtrd.mm"
include "muldvds1.mm"
include "syl6breqr.mm"

theorem etransclem28
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let vj: setvar j
  let vn: setvar n
  let cJ: class J
  let cM: class M
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume etransclem28.p: |- ( ph -> P e. NN )
  assume etransclem28.m: |- ( ph -> M e. NN0 )
  assume etransclem28.n: |- ( ph -> N e. NN0 )
  assume etransclem28.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem28.d: |- ( ph -> D e. ( C ` N ) )
  assume etransclem28.j: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem28.t: |- T = ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( D ` j ) ) ) x. ( if ( ( P - 1 ) < ( D ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( D ` 0 ) ) ) ) x. ( J ^ ( ( P - 1 ) - ( D ` 0 ) ) ) ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( D ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( D ` j ) ) ) ) x. ( ( J - j ) ^ ( P - ( D ` j ) ) ) ) ) ) )

  disjoint D c
  disjoint D j
  disjoint c j
  disjoint J j
  disjoint M c
  disjoint M j
  disjoint M n
  disjoint c n
  disjoint j n
  disjoint N c
  disjoint N n
  disjoint P j
  disjoint j ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( ! ` ( P - 1 ) ) || T )

  proof
    wph
    cP
    c1
    cmin
    co
    #
    cfa
    cfv
    #
    cN
    cfa
    cfv
    #
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    cD
    cfv
    #
    cfa
    cfv
    vj
    cprod
    #
    cdiv
    co
    #
    @0
    cc0
    cD
    cfv
    #
    clt
    wbr
    cc0
    @1
    @0
    @8
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @9
    cexp
    co
    cmul
    co
    cif
    c1
    cM
    cfz
    co
    #
    cP
    @5
    clt
    wbr
    #
    cc0
    cP
    cfa
    cfv
    #
    cP
    @5
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    cJ
    @4
    cmin
    co
    #
    @13
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    cmul
    co
    #
    cT
    cdvds
    wph
    cJ
    cc0
    wceq
    #
    @1
    @20
    cdvds
    wbr
    #
    wph
    @21
    wa
    #
    @8
    @0
    wceq
    #
    @22
    @23
    @24
    wa
    #
    @1
    @7
    @1
    @10
    @11
    cc0
    @14
    @4
    cneg
    #
    @13
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    #
    cmul
    co
    #
    @20
    cdvds
    @23
    @1
    @32
    cdvds
    wbr
    #
    @24
    @23
    @1
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @31
    cz
    wcel
    #
    w3a
    @1
    @31
    cdvds
    wbr
    #
    @33
    @23
    @34
    @35
    @36
    wph
    @34
    @21
    wph
    @1
    wph
    @0
    wph
    cP
    cn
    wcel
    #
    @0
    cn0
    wcel
    #
    etransclem28.p
    cP
    nnm1nn0
    syl
    #
    faccld
    nnzd
    #
    adantr
    #
    wph
    @35
    @21
    wph
    @7
    wph
    @7
    @3
    @5
    vj
    csu
    #
    cfa
    cfv
    #
    @6
    cdiv
    co
    cn
    wph
    @2
    @44
    @6
    cdiv
    wph
    cN
    @43
    cfa
    wph
    @43
    cN
    wph
    cD
    @3
    @4
    vc
    cv
    #
    cfv
    #
    vj
    csu
    #
    cN
    wceq
    #
    vc
    cc0
    cN
    cfz
    co
    #
    @3
    cmap
    co
    #
    crab
    #
    wcel
    #
    @43
    cN
    wceq
    #
    wph
    cD
    cN
    cC
    cfv
    @51
    etransclem28.d
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem28.c
    etransclem28.n
    etransclem12
    eleqtrd
    #
    @52
    cD
    @50
    wcel
    #
    @53
    @48
    @53
    vc
    cD
    @50
    @45
    cD
    wceq
    #
    @47
    @43
    cN
    @56
    @3
    @46
    @5
    vj
    @4
    @45
    cD
    fveq1
    sumeq2ad
    eqeq1d
    elrab
    simprbi
    syl
    #
    eqcomd
    fveq2d
    oveq1d
    wph
    @3
    cD
    vj
    vj
    cD
    nfcv
    wph
    cc0
    cM
    fzfid
    wph
    @52
    cD
    cn0
    @3
    cmap
    co
    #
    wcel
    @54
    @52
    @50
    @58
    cD
    @52
    cn0
    cvv
    wcel
    @49
    cn0
    wss
    #
    @50
    @58
    wss
    nn0ex
    @59
    @52
    cN
    fzssnn0
    a1i
    @49
    cn0
    @3
    cvv
    mapss
    sylancr
    @48
    vc
    cD
    @50
    elrabi
    #
    sseldd
    syl
    mccl
    eqeltrd
    nnzd
    adantr
    @23
    @1
    @30
    @42
    @23
    @30
    @19
    cz
    @21
    @30
    @19
    wceq
    wph
    @21
    @10
    @29
    @18
    vj
    @21
    @11
    @28
    @17
    cc0
    @21
    @27
    @16
    @14
    cmul
    @21
    @26
    @15
    @13
    cexp
    @21
    @15
    cc0
    @4
    cmin
    co
    @26
    cJ
    cc0
    @4
    cmin
    oveq1
    @4
    df-neg
    syl6reqr
    oveq1d
    oveq2d
    ifeq2d
    prodeq2ad
    adantl
    wph
    @19
    cz
    wcel
    @21
    wph
    cD
    cP
    vj
    cJ
    cM
    cN
    etransclem28.p
    wph
    @55
    @3
    @49
    cD
    wf
    #
    wph
    @52
    @55
    @54
    @60
    syl
    cD
    @49
    @3
    elmapi
    syl
    #
    etransclem28.j
    etransclem7
    adantr
    eqeltrd
    #
    zmulcld
    3jca
    @23
    @34
    @30
    cz
    wcel
    @37
    @42
    @63
    @1
    @30
    dvdsmul1
    syl2anc
    @1
    @7
    @31
    dvdsmultr2
    sylc
    adantr
    @25
    cD
    cP
    @20
    vj
    cJ
    cM
    cN
    wph
    @38
    @21
    @24
    etransclem28.p
    ad2antrr
    wph
    cM
    cn0
    wcel
    #
    @21
    @24
    etransclem28.m
    ad2antrr
    wph
    @61
    @21
    @24
    @62
    ad2antrr
    @20
    eqid
    #
    wph
    @21
    @24
    simplr
    @23
    @24
    simpr
    etransclem14
    breqtrrd
    @23
    @24
    wn
    #
    wa
    #
    @1
    cc0
    @20
    cdvds
    wph
    @1
    cc0
    cdvds
    wbr
    #
    @21
    @66
    wph
    @34
    @68
    @41
    @1
    dvds0
    syl
    ad2antrr
    @67
    cD
    cP
    @20
    vj
    cJ
    cM
    cN
    wph
    @38
    @21
    @66
    etransclem28.p
    ad2antrr
    wph
    @64
    @21
    @66
    etransclem28.m
    ad2antrr
    wph
    cN
    cn0
    wcel
    #
    @21
    @66
    etransclem28.n
    ad2antrr
    wph
    @61
    @21
    @66
    @62
    ad2antrr
    @65
    wph
    @21
    @66
    simplr
    @66
    @8
    @0
    wne
    @23
    @8
    @0
    neqne
    adantl
    etransclem15
    breqtrrd
    pm2.61dan
    wph
    @21
    wn
    #
    wa
    #
    @34
    cP
    cz
    wcel
    #
    @20
    cz
    wcel
    #
    w3a
    #
    @1
    cP
    cmul
    co
    #
    @20
    cdvds
    wbr
    @22
    wph
    @74
    @70
    wph
    @34
    @72
    @73
    @41
    wph
    cP
    etransclem28.p
    nnzd
    wph
    cC
    cD
    cP
    vj
    vn
    cJ
    cM
    cN
    vc
    etransclem28.p
    etransclem28.m
    etransclem28.n
    wph
    cJ
    wph
    cJ
    @3
    wcel
    #
    cJ
    cn0
    wcel
    #
    etransclem28.j
    cJ
    cM
    elfznn0
    syl
    #
    nn0zd
    #
    etransclem28.c
    etransclem28.d
    etransclem26
    3jca
    adantr
    @71
    @75
    @12
    @20
    cdvds
    wph
    @75
    @12
    wceq
    @70
    wph
    @12
    @0
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @1
    @80
    cmul
    co
    #
    @75
    wph
    cP
    @80
    cfa
    wph
    @80
    cP
    wph
    cP
    c1
    wph
    cP
    etransclem28.p
    nncnd
    wph
    1cnd
    npcand
    #
    eqcomd
    fveq2d
    wph
    @39
    @81
    @82
    wceq
    @40
    @0
    facp1
    syl
    wph
    @80
    cP
    @1
    cmul
    @83
    oveq2d
    3eqtrrd
    adantr
    @71
    cD
    cP
    @20
    vj
    cJ
    cM
    cN
    wph
    @38
    @70
    etransclem28.p
    adantr
    wph
    @64
    @70
    etransclem28.m
    adantr
    wph
    @69
    @70
    etransclem28.n
    adantr
    wph
    @61
    @70
    @62
    adantr
    wph
    @53
    @70
    @57
    adantr
    @65
    @71
    c1
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cJ
    cz
    wcel
    #
    w3a
    #
    c1
    cJ
    cle
    wbr
    #
    cJ
    cM
    cle
    wbr
    #
    wa
    wa
    cJ
    @10
    wcel
    @71
    @87
    @88
    @89
    @71
    @84
    @85
    @86
    @71
    1zzd
    wph
    @85
    @70
    wph
    cM
    etransclem28.m
    nn0zd
    adantr
    wph
    @86
    @70
    @79
    adantr
    3jca
    @71
    cJ
    @71
    @77
    cJ
    cc0
    wne
    #
    cJ
    cn
    wcel
    wph
    @77
    @70
    @78
    adantr
    @70
    @90
    wph
    cJ
    cc0
    neqne
    adantl
    cJ
    elnnne0
    sylanbrc
    nnge1d
    wph
    @89
    @70
    wph
    @76
    @89
    etransclem28.j
    cJ
    cc0
    cM
    elfzle2
    syl
    adantr
    jca32
    cJ
    c1
    cM
    elfz2
    sylibr
    etransclem25
    eqbrtrd
    @1
    cP
    @20
    muldvds1
    sylc
    pm2.61dan
    etransclem28.t
    syl6breqr
end
