include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cdvds.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "csup.mm"
include "wss.mm"
include "wral.mm"
include "wrex.mm"
include "c0.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "3ad2ant1.mm"
include "zmulcl.mm"
include "ad2ant2r.mm"
include "3adant1.mm"
include "cc.mm"
include "zcn.mm"
include "anim1i.mm"
include "mulne0.mm"
include "syl2an.mm"
include "eqid.mm"
include "pclem.mm"
include "syl12anc.mm"
include "simp1d.mm"
include "simp3d.mm"
include "simp2l.mm"
include "simp2r.mm"
include "pcprecl.mm"
include "simpld.mm"
include "simp3l.mm"
include "simp3r.mm"
include "nn0addcld.mm"
include "cn.mm"
include "prmnn.mm"
include "nncnd.mm"
include "expaddd.mm"
include "simprd.mm"
include "wi.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "dvdsmulc.mm"
include "syl3anc.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "dvdscmul.mm"
include "zmulcld.mm"
include "dvdstr.mm"
include "mp2and.mm"
include "oveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "cbvrabv.mm"
include "syl6eleq.mm"
include "suprzub.mm"
include "syl6breqr.mm"
include "cdiv.mm"
include "wo.mm"
include "pcprendvds2.mm"
include "ioran.mm"
include "wb.mm"
include "simp1.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "mpbid.mm"
include "euclemma.mm"
include "mtbird.mm"
include "c1.mm"
include "nn0ltp1le.mm"
include "syl2anc.mm"
include "peano2nn0.mm"
include "syl.mm"
include "dvdsexp.mm"
include "3expia.mm"
include "mpan2d.mm"
include "syld.mm"
include "nn0zd.mm"
include "eluz.mm"
include "expp1d.mm"
include "zcnd.mm"
include "mulcld.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "divmuldivd.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"
include "breq12d.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "bitrd.mm"
include "3imtr3d.mm"
include "sylbid.mm"
include "mtod.mm"
include "nn0red.mm"
include "eqleltd.mm"
include "mpbir2and.mm"

theorem pcpremul
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume pcpremul.1: |- S = sup ( { n e. NN0 | ( P ^ n ) || M } , RR , < )
  assume pcpremul.2: |- T = sup ( { n e. NN0 | ( P ^ n ) || N } , RR , < )
  assume pcpremul.3: |- U = sup ( { n e. NN0 | ( P ^ n ) || ( M x. N ) } , RR , < )

  disjoint M n
  disjoint N n
  disjoint P n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint P x
  disjoint P y
  disjoint S x
  disjoint T x
  assert |- ( ( P e. Prime /\ ( M e. ZZ /\ M =/= 0 ) /\ ( N e. ZZ /\ N =/= 0 ) ) -> ( S + T ) = U )

  proof
    cP
    cprime
    wcel
    #
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    #
    wa
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cS
    cT
    caddc
    co
    #
    cU
    wceq
    @8
    cU
    cle
    wbr
    @8
    cU
    clt
    wbr
    #
    wn
    @7
    @8
    cP
    vn
    cv
    #
    cexp
    co
    #
    cM
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cU
    cle
    @7
    @14
    cz
    wss
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    vy
    @14
    wral
    vx
    cz
    wrex
    #
    @8
    @14
    wcel
    @8
    @15
    cle
    wbr
    @7
    @16
    @14
    c0
    wne
    #
    @18
    @7
    cP
    c2
    cuz
    cfv
    wcel
    #
    @12
    cz
    wcel
    #
    @12
    cc0
    wne
    #
    @16
    @19
    @18
    w3a
    @0
    @3
    @20
    @6
    cP
    prmuz2
    3ad2ant1
    #
    @3
    @6
    @21
    @0
    @1
    @4
    @21
    @2
    @5
    cM
    cN
    zmulcl
    ad2ant2r
    3adant1
    #
    @3
    @6
    @22
    @0
    @3
    cM
    cc
    wcel
    #
    @2
    wa
    cN
    cc
    wcel
    #
    @5
    wa
    @22
    @6
    @1
    @25
    @2
    cM
    zcn
    anim1i
    @4
    @26
    @5
    cN
    zcn
    anim1i
    cM
    cN
    mulne0
    syl2an
    3adant1
    #
    vx
    vy
    @14
    cP
    vn
    @12
    @14
    eqid
    #
    pclem
    syl12anc
    #
    simp1d
    @7
    @16
    @19
    @18
    @29
    simp3d
    @7
    @8
    cP
    @17
    cexp
    co
    #
    @12
    cdvds
    wbr
    #
    vx
    cn0
    crab
    #
    @14
    @7
    @8
    cn0
    wcel
    #
    cP
    @8
    cexp
    co
    #
    @12
    cdvds
    wbr
    #
    @8
    @32
    wcel
    @7
    cS
    cT
    @7
    cS
    cn0
    wcel
    #
    cP
    cS
    cexp
    co
    #
    cM
    cdvds
    wbr
    #
    @7
    @20
    @1
    @2
    @36
    @38
    wa
    @23
    @0
    @1
    @2
    @6
    simp2l
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    @11
    cM
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cP
    cS
    vn
    cM
    @41
    eqid
    #
    pcpremul.1
    pcprecl
    syl12anc
    #
    simpld
    #
    @7
    cT
    cn0
    wcel
    #
    cP
    cT
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @7
    @20
    @4
    @5
    @45
    @47
    wa
    @23
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    @11
    cN
    cdvds
    wbr
    vn
    cn0
    crab
    #
    cP
    cT
    vn
    cN
    @50
    eqid
    #
    pcpremul.2
    pcprecl
    syl12anc
    #
    simpld
    #
    nn0addcld
    #
    @7
    @34
    cM
    @46
    cmul
    co
    #
    cdvds
    wbr
    #
    @55
    @12
    cdvds
    wbr
    #
    @35
    @7
    @34
    @37
    @46
    cmul
    co
    #
    @55
    cdvds
    @7
    cP
    cS
    cT
    @7
    cP
    @0
    @3
    cP
    cn
    wcel
    @6
    cP
    prmnn
    3ad2ant1
    #
    nncnd
    #
    @53
    @44
    expaddd
    #
    @7
    @38
    @58
    @55
    cdvds
    wbr
    #
    @7
    @36
    @38
    @43
    simprd
    #
    @7
    @37
    cz
    wcel
    #
    @1
    @46
    cz
    wcel
    #
    @38
    @62
    wi
    @7
    @37
    @7
    cP
    cS
    @59
    @44
    nnexpcld
    #
    nnzd
    #
    @39
    @7
    @46
    @7
    cP
    cT
    @59
    @53
    nnexpcld
    #
    nnzd
    #
    @46
    @37
    cM
    dvdsmulc
    syl3anc
    mpd
    eqbrtrd
    @7
    @47
    @57
    @7
    @45
    @47
    @52
    simprd
    #
    @7
    @65
    @4
    @1
    @47
    @57
    wi
    @69
    @48
    @39
    cM
    @46
    cN
    dvdscmul
    syl3anc
    mpd
    @7
    @34
    cz
    wcel
    #
    @55
    cz
    wcel
    @21
    @56
    @57
    wa
    @35
    wi
    @7
    @34
    @7
    cP
    @8
    @59
    @54
    nnexpcld
    #
    nnzd
    #
    @7
    cM
    @46
    @39
    @69
    zmulcld
    @24
    @34
    @55
    @12
    dvdstr
    syl3anc
    mp2and
    @31
    @35
    vx
    @8
    cn0
    @17
    @8
    wceq
    @30
    @34
    @12
    cdvds
    @17
    @8
    cP
    cexp
    oveq2
    breq1d
    elrab
    sylanbrc
    @31
    @13
    vx
    vn
    cn0
    @17
    @10
    wceq
    @30
    @11
    @12
    cdvds
    @17
    @10
    cP
    cexp
    oveq2
    breq1d
    cbvrabv
    syl6eleq
    vx
    vy
    @14
    @8
    suprzub
    syl3anc
    pcpremul.3
    syl6breqr
    @7
    @9
    cP
    cM
    @37
    cdiv
    co
    #
    cN
    @46
    cdiv
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @7
    @77
    cP
    @74
    cdvds
    wbr
    #
    cP
    @75
    cdvds
    wbr
    #
    wo
    #
    @7
    @78
    wn
    #
    @79
    wn
    #
    @80
    wn
    @7
    @20
    @1
    @2
    @81
    @23
    @39
    @40
    @41
    cP
    cS
    vn
    cM
    @42
    pcpremul.1
    pcprendvds2
    syl12anc
    @7
    @20
    @4
    @5
    @82
    @23
    @48
    @49
    @50
    cP
    cT
    vn
    cN
    @51
    pcpremul.2
    pcprendvds2
    syl12anc
    @78
    @79
    ioran
    sylanbrc
    @7
    @0
    @74
    cz
    wcel
    #
    @75
    cz
    wcel
    #
    @77
    @80
    wb
    @0
    @3
    @6
    simp1
    @7
    @38
    @83
    @63
    @7
    @64
    @37
    cc0
    wne
    @1
    @38
    @83
    wb
    @67
    @7
    @37
    @66
    nnne0d
    #
    @39
    @37
    cM
    dvdsval2
    syl3anc
    mpbid
    #
    @7
    @47
    @84
    @70
    @7
    @65
    @46
    cc0
    wne
    @4
    @47
    @84
    wb
    @69
    @7
    @46
    @68
    nnne0d
    #
    @48
    @46
    cN
    dvdsval2
    syl3anc
    mpbid
    #
    cP
    @74
    @75
    euclemma
    syl3anc
    mtbird
    @7
    @9
    @8
    c1
    caddc
    co
    #
    cU
    cle
    wbr
    #
    @77
    @7
    @33
    cU
    cn0
    wcel
    #
    @9
    @90
    wb
    @54
    @7
    @91
    cP
    cU
    cexp
    co
    #
    @12
    cdvds
    wbr
    #
    @7
    @20
    @21
    @22
    @91
    @93
    wa
    @23
    @24
    @27
    @14
    cP
    cU
    vn
    @12
    @28
    pcpremul.3
    pcprecl
    syl12anc
    #
    simpld
    #
    @8
    cU
    nn0ltp1le
    syl2anc
    @7
    cU
    @89
    cuz
    cfv
    wcel
    #
    cP
    @89
    cexp
    co
    #
    @12
    cdvds
    wbr
    #
    @90
    @77
    @7
    @96
    @97
    @92
    cdvds
    wbr
    #
    @98
    @7
    cP
    cz
    wcel
    #
    @89
    cn0
    wcel
    #
    @96
    @99
    wi
    @7
    cP
    @59
    nnzd
    #
    @7
    @33
    @101
    @54
    @8
    peano2nn0
    syl
    #
    @100
    @101
    @96
    @99
    cP
    @89
    cU
    dvdsexp
    3expia
    syl2anc
    @7
    @99
    @93
    @98
    @7
    @91
    @93
    @94
    simprd
    @7
    @97
    cz
    wcel
    @92
    cz
    wcel
    @21
    @99
    @93
    wa
    @98
    wi
    @7
    @97
    @7
    cP
    @89
    @59
    @103
    nnexpcld
    nnzd
    @7
    @92
    @7
    cP
    cU
    @59
    @95
    nnexpcld
    nnzd
    @24
    @97
    @92
    @12
    dvdstr
    syl3anc
    mpan2d
    syld
    @7
    @89
    cz
    wcel
    cU
    cz
    wcel
    @96
    @90
    wb
    @7
    @89
    @103
    nn0zd
    @7
    cU
    @95
    nn0zd
    @89
    cU
    eluz
    syl2anc
    @7
    @98
    @34
    cP
    cmul
    co
    #
    @34
    @76
    cmul
    co
    #
    cdvds
    wbr
    #
    @77
    @7
    @97
    @104
    @12
    @105
    cdvds
    @7
    cP
    @8
    @60
    @54
    expp1d
    @7
    @34
    @12
    @34
    cdiv
    co
    #
    cmul
    co
    @12
    @105
    @7
    @12
    @34
    @7
    cM
    cN
    @7
    cM
    @39
    zcnd
    #
    @7
    cN
    @48
    zcnd
    #
    mulcld
    @7
    @34
    @72
    nncnd
    @7
    @34
    @72
    nnne0d
    #
    divcan2d
    @7
    @107
    @76
    @34
    cmul
    @7
    @107
    @12
    @58
    cdiv
    co
    @76
    @7
    @34
    @58
    @12
    cdiv
    @61
    oveq2d
    @7
    cM
    @37
    cN
    @46
    @108
    @7
    @37
    @66
    nncnd
    @109
    @7
    @46
    @68
    nncnd
    @85
    @87
    divmuldivd
    eqtr4d
    oveq2d
    eqtr3d
    breq12d
    @7
    @100
    @76
    cz
    wcel
    @71
    @34
    cc0
    wne
    @106
    @77
    wb
    @102
    @7
    @74
    @75
    @86
    @88
    zmulcld
    @73
    @110
    @34
    cP
    @76
    dvdscmulr
    syl112anc
    bitrd
    3imtr3d
    sylbid
    mtod
    @7
    @8
    cU
    @7
    @8
    @54
    nn0red
    @7
    cU
    @95
    nn0red
    eqleltd
    mpbir2and
end
