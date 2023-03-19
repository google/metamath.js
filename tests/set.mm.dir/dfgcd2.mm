include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "gcdcl.mm"
include "nn0ge0d.mm"
include "gcddvds.mm"
include "3anass.mm"
include "ancom.mm"
include "bitri.mm"
include "dvdsgcd.mm"
include "sylbir.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "adantl.mm"
include "mpbird.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "gcdval.mm"
include "iftrue.mm"
include "bi2anan9.mm"
include "imbi1d.mm"
include "3anbi23d.mm"
include "dvdszrcl.mm"
include "dvds0.mm"
include "jca.mm"
include "pm5.5.mm"
include "syl.mm"
include "ralbidva.mm"
include "0z.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "0dvds.mm"
include "biimpd.mm"
include "eqcom.mm"
include "syl6ibr.mm"
include "syl5.mm"
include "sylbid.mm"
include "ex.mm"
include "com12.mm"
include "3imp.mm"
include "syl6bi.mm"
include "adantld.mm"
include "imp.mm"
include "eqtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "simpld.mm"
include "zred.mm"
include "3ad2ant2.mm"
include "ad2antll.mm"
include "elrab.mm"
include "imbi12d.mm"
include "com23.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "elnn0z.mm"
include "simplbi2.mm"
include "impcom.mm"
include "cn.mm"
include "simp-4l.mm"
include "wo.mm"
include "elnn0.mm"
include "2a1.mm"
include "anbi2d.mm"
include "ianor.mm"
include "pm2.24.mm"
include "mpcom.mm"
include "jaoi.mm"
include "sylbi.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "exp31.mm"
include "com14.mm"
include "zre.mm"
include "ad2antlr.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "mpan2d.mm"
include "com13.mm"
include "syld.mm"
include "expimpd.mm"
include "ancri.mm"
include "sylibr.mm"
include "simprr.mm"
include "rspcedvd.mm"
include "eqsupd.mm"
include "pm2.61ian.mm"
include "eqtr2d.mm"
include "impbida.mm"

theorem dfgcd2
  let cD: class D
  let ve: setvar e
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z

  disjoint D e
  disjoint M e
  disjoint N e
  disjoint D n
  disjoint D y
  disjoint D z
  disjoint e n
  disjoint e y
  disjoint e z
  disjoint n y
  disjoint n z
  disjoint y z
  disjoint M n
  disjoint M y
  disjoint M z
  disjoint N n
  disjoint N y
  disjoint N z
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( D = ( M gcd N ) <-> ( 0 <_ D /\ ( D || M /\ D || N ) /\ A. e e. ZZ ( ( e || M /\ e || N ) -> e || D ) ) ) )

  proof
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
    cD
    cM
    cN
    cgcd
    co
    #
    wceq
    #
    cc0
    cD
    cle
    wbr
    #
    cD
    cM
    cdvds
    wbr
    #
    cD
    cN
    cdvds
    wbr
    #
    wa
    #
    ve
    cv
    #
    cM
    cdvds
    wbr
    #
    @9
    cN
    cdvds
    wbr
    #
    wa
    #
    @9
    cD
    cdvds
    wbr
    #
    wi
    #
    ve
    cz
    wral
    #
    w3a
    #
    @2
    @4
    wa
    @16
    cc0
    @3
    cle
    wbr
    #
    @3
    cM
    cdvds
    wbr
    #
    @3
    cN
    cdvds
    wbr
    #
    wa
    #
    @12
    @9
    @3
    cdvds
    wbr
    #
    wi
    #
    ve
    cz
    wral
    #
    w3a
    #
    @2
    @24
    @4
    @2
    @17
    @20
    @23
    @2
    @3
    cM
    cN
    gcdcl
    nn0ge0d
    cM
    cN
    gcddvds
    @2
    @22
    ve
    cz
    @2
    @9
    cz
    wcel
    #
    wa
    #
    @25
    @0
    @1
    w3a
    #
    @22
    @27
    @25
    @2
    wa
    @26
    @25
    @0
    @1
    3anass
    @25
    @2
    ancom
    bitri
    @9
    cM
    cN
    dvdsgcd
    sylbir
    ralrimiva
    3jca
    adantr
    @4
    @16
    @24
    wb
    @2
    @4
    @5
    @17
    @8
    @20
    @15
    @23
    cD
    @3
    cc0
    cle
    breq2
    @4
    @6
    @18
    @7
    @19
    cD
    @3
    cM
    cdvds
    breq1
    cD
    @3
    cN
    cdvds
    breq1
    anbi12d
    @4
    @14
    @22
    ve
    cz
    @4
    @13
    @21
    @12
    cD
    @3
    @9
    cdvds
    breq2
    imbi2d
    ralbidv
    3anbi123d
    adantl
    mpbird
    @2
    @16
    wa
    #
    @3
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    #
    cc0
    vn
    cv
    #
    cM
    cdvds
    wbr
    #
    @32
    cN
    cdvds
    wbr
    #
    wa
    #
    vn
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    #
    cD
    @2
    @3
    @38
    wceq
    @16
    vn
    cM
    cN
    gcdval
    adantr
    @31
    @28
    @38
    cD
    wceq
    @31
    @28
    wa
    @38
    cc0
    cD
    @31
    @38
    cc0
    wceq
    @28
    @31
    cc0
    @37
    iftrue
    adantr
    @31
    @28
    cc0
    cD
    wceq
    #
    @31
    @16
    @39
    @2
    @31
    @16
    @5
    cD
    cc0
    cdvds
    wbr
    #
    @40
    wa
    #
    @9
    cc0
    cdvds
    wbr
    #
    @42
    wa
    #
    @13
    wi
    #
    ve
    cz
    wral
    #
    w3a
    @39
    @31
    @8
    @41
    @15
    @45
    @5
    @29
    @6
    @40
    @30
    @7
    @40
    cM
    cc0
    cD
    cdvds
    breq2
    cN
    cc0
    cD
    cdvds
    breq2
    bi2anan9
    @31
    @14
    @44
    ve
    cz
    @31
    @12
    @43
    @13
    @29
    @10
    @42
    @30
    @11
    @42
    cM
    cc0
    @9
    cdvds
    breq2
    cN
    cc0
    @9
    cdvds
    breq2
    bi2anan9
    imbi1d
    ralbidv
    3anbi23d
    @5
    @41
    @45
    @39
    @41
    @5
    @45
    @39
    wi
    #
    @40
    @5
    @46
    wi
    #
    @40
    @40
    cD
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    wa
    @47
    cD
    cc0
    dvdszrcl
    @48
    @47
    @49
    @48
    @5
    @46
    @48
    @5
    wa
    #
    @45
    @13
    ve
    cz
    wral
    #
    @39
    @50
    @44
    @13
    ve
    cz
    @50
    @25
    wa
    @43
    @44
    @13
    wb
    @25
    @43
    @50
    @25
    @42
    @42
    @9
    dvds0
    #
    @52
    jca
    adantl
    @43
    @13
    pm5.5
    syl
    ralbidva
    @48
    @51
    @39
    wi
    @5
    @51
    cc0
    cD
    cdvds
    wbr
    #
    @48
    @39
    @49
    @51
    @53
    wi
    0z
    @13
    @53
    ve
    cc0
    cz
    @9
    cc0
    cD
    cdvds
    breq1
    rspcv
    ax-mp
    @48
    @53
    cD
    cc0
    wceq
    #
    @39
    @48
    @53
    @54
    cD
    0dvds
    biimpd
    cc0
    cD
    eqcom
    syl6ibr
    syl5
    adantr
    sylbid
    ex
    adantr
    syl
    adantr
    com12
    3imp
    syl6bi
    adantld
    imp
    eqtrd
    @31
    wn
    #
    @28
    wa
    #
    @38
    @37
    cD
    @55
    @38
    @37
    wceq
    @28
    @31
    cc0
    @37
    iffalse
    adantr
    @56
    vy
    vz
    cr
    @36
    cD
    clt
    cr
    clt
    wor
    @56
    ltso
    a1i
    @16
    cD
    cr
    wcel
    #
    @55
    @2
    @8
    @5
    @57
    @15
    @6
    @57
    @7
    @6
    cD
    @6
    @48
    @0
    cD
    cM
    dvdszrcl
    #
    simpld
    #
    zred
    adantr
    #
    3ad2ant2
    ad2antll
    vy
    cv
    #
    @36
    wcel
    #
    @56
    cD
    @61
    clt
    wbr
    wn
    #
    @62
    @61
    cz
    wcel
    #
    @61
    cM
    cdvds
    wbr
    #
    @61
    cN
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @56
    @63
    wi
    @35
    @67
    vn
    @61
    cz
    @32
    @61
    wceq
    @33
    @65
    @34
    @66
    @32
    @61
    cM
    cdvds
    breq1
    @32
    @61
    cN
    cdvds
    breq1
    anbi12d
    elrab
    @68
    @55
    @28
    @63
    @68
    @55
    wa
    #
    @2
    @16
    @63
    @16
    @69
    @2
    wa
    #
    @63
    @5
    @8
    @15
    @70
    @63
    wi
    #
    @5
    @8
    @15
    @71
    wi
    @70
    @15
    @5
    @8
    wa
    #
    @63
    @70
    @15
    @61
    cD
    cdvds
    wbr
    #
    @72
    @63
    wi
    #
    @68
    @15
    @73
    wi
    #
    @55
    @2
    @64
    @67
    @75
    @64
    @15
    @67
    @73
    @14
    @67
    @73
    wi
    ve
    @61
    cz
    @9
    @61
    wceq
    #
    @12
    @67
    @13
    @73
    @76
    @10
    @65
    @11
    @66
    @9
    @61
    cM
    cdvds
    breq1
    @9
    @61
    cN
    cdvds
    breq1
    anbi12d
    @9
    @61
    cD
    cdvds
    breq1
    imbi12d
    rspcv
    com23
    imp
    ad2antrr
    @69
    @73
    @74
    wi
    @2
    @72
    @73
    @69
    @63
    @72
    @73
    cD
    cn0
    wcel
    #
    @69
    @63
    wi
    @8
    @5
    @77
    @6
    @5
    @77
    wi
    #
    @7
    @6
    @48
    @0
    wa
    @78
    @58
    @48
    @78
    @0
    @77
    @48
    @5
    cD
    elnn0z
    simplbi2
    adantr
    syl
    adantr
    impcom
    @72
    @73
    @77
    wa
    #
    @69
    @63
    @72
    @79
    wa
    #
    @69
    wa
    @61
    cD
    cle
    wbr
    #
    @63
    @80
    @69
    @81
    @79
    @72
    @69
    @81
    wi
    #
    @73
    @77
    @72
    @82
    wi
    @69
    @77
    @72
    @73
    @81
    @69
    @77
    @72
    @73
    @81
    wi
    #
    @69
    @77
    wa
    #
    @72
    wa
    @64
    cD
    cn
    wcel
    #
    @83
    @64
    @67
    @55
    @77
    @72
    simp-4l
    @84
    @72
    @85
    @77
    @69
    @72
    @85
    wi
    #
    @77
    @85
    @54
    wo
    @69
    @86
    wi
    #
    cD
    elnn0
    @85
    @87
    @54
    @85
    @69
    @72
    2a1
    @54
    @69
    @86
    @54
    @69
    wa
    @72
    @5
    cc0
    cM
    cdvds
    wbr
    #
    cc0
    cN
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    @85
    @54
    @72
    @91
    wb
    @69
    @54
    @8
    @90
    @5
    @54
    @6
    @88
    @7
    @89
    cD
    cc0
    cM
    cdvds
    breq1
    cD
    cc0
    cN
    cdvds
    breq1
    anbi12d
    anbi2d
    adantr
    @55
    @91
    @85
    wi
    @54
    @68
    @55
    @90
    @85
    @5
    @55
    @29
    wn
    #
    @30
    wn
    #
    wo
    @90
    @85
    wi
    #
    @29
    @30
    ianor
    @92
    @94
    @93
    @90
    @92
    @85
    @88
    @92
    @85
    wi
    #
    @89
    @49
    @0
    wa
    @88
    @95
    cc0
    cM
    dvdszrcl
    @0
    @88
    @95
    wi
    @49
    @0
    @88
    @29
    @95
    cM
    0dvds
    @29
    @85
    pm2.24
    syl6bi
    adantl
    mpcom
    adantr
    com12
    @90
    @93
    @85
    @89
    @93
    @85
    wi
    #
    @88
    @49
    @1
    wa
    @89
    @96
    cc0
    cN
    dvdszrcl
    @1
    @89
    @96
    wi
    @49
    @1
    @89
    @30
    @96
    cN
    0dvds
    @30
    @85
    pm2.24
    syl6bi
    adantl
    mpcom
    adantl
    com12
    jaoi
    sylbi
    adantld
    ad2antll
    sylbid
    ex
    jaoi
    sylbi
    impcom
    imp
    @61
    cD
    dvdsle
    syl2anc
    exp31
    com14
    imp
    impcom
    imp
    @69
    @61
    cr
    wcel
    #
    @57
    @81
    @63
    wb
    @80
    @64
    @97
    @67
    @55
    @61
    zre
    ad2antrr
    @8
    @57
    @5
    @79
    @60
    ad2antlr
    @61
    cD
    lenlt
    syl2anr
    mpbid
    exp31
    mpan2d
    com13
    adantr
    syld
    com13
    ex
    3imp
    com12
    expimpd
    expimpd
    sylbi
    impcom
    @56
    @97
    @61
    cD
    clt
    wbr
    #
    wa
    #
    wa
    #
    @61
    vz
    cv
    #
    clt
    wbr
    #
    @98
    vz
    cD
    @36
    @100
    @48
    @8
    wa
    #
    cD
    @36
    wcel
    @56
    @103
    @99
    @16
    @103
    @55
    @2
    @8
    @5
    @103
    @15
    @8
    @48
    @6
    @48
    @7
    @59
    adantr
    ancri
    3ad2ant2
    ad2antll
    adantr
    @35
    @8
    vn
    cD
    cz
    @32
    cD
    wceq
    @33
    @6
    @34
    @7
    @32
    cD
    cM
    cdvds
    breq1
    @32
    cD
    cN
    cdvds
    breq1
    anbi12d
    elrab
    sylibr
    @101
    cD
    wceq
    @102
    @98
    wb
    @100
    @101
    cD
    @61
    clt
    breq2
    adantl
    @56
    @97
    @98
    simprr
    rspcedvd
    eqsupd
    eqtrd
    pm2.61ian
    eqtr2d
    impbida
end
