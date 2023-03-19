include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "crp.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "simpr.mm"
include "nn0ge0.mm"
include "adantr.mm"
include "cr.mm"
include "nn0re.mm"
include "0red.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "fveq2d.mm"
include "cpi.mm"
include "c2.mm"
include "cuz.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "wallispilem2.mm"
include "simp1i.mm"
include "pirp.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "ex.mm"
include "rgen.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpllr.mm"
include "simplr.mm"
include "rsp.mm"
include "sylc.mm"
include "fveq2.mm"
include "simp2i.mm"
include "2rp.mm"
include "a1i.mm"
include "simp3i.mm"
include "adantl.mm"
include "cn.mm"
include "eluz2nn.mm"
include "nnre.mm"
include "1red.mm"
include "resubcld.mm"
include "syl.mm"
include "clt.mm"
include "1m1e0.mm"
include "eluzelre.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "ltsub1dd.mm"
include "syl5eqbrr.mm"
include "elrpd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "breq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "ad3antlr.mm"
include "uznn0sub.mm"
include "jca.mm"
include "simplll.mm"
include "w3a.mm"
include "simp2.mm"
include "oveq1d.mm"
include "cc.mm"
include "3ad2ant1.mm"
include "recnd.mm"
include "df-2.mm"
include "oveq2d.mm"
include "id.mm"
include "1cnd.mm"
include "pnpcan2d.mm"
include "eqtrd.mm"
include "lem1d.mm"
include "eqbrtrd.mm"
include "syl3anc.mm"
include "rspccva.mm"
include "rpmulcld.mm"
include "eqeltrd.mm"
include "adantllr.mm"
include "wo.mm"
include "simp3.mm"
include "nn0p1nn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "uzp1.mm"
include "1p1e2.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "orbi2i.mm"
include "mpjaod.mm"
include "adantlr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "3ad2antl1.mm"
include "simpl3.mm"
include "wb.mm"
include "wne.mm"
include "simp1.mm"
include "3ad2ant2.mm"
include "nnm1ge0.mm"
include "ltsubaddd.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "gt0ne0d.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "nnleltp1.mm"
include "syl2anc.mm"
include "elnn0.mm"
include "orcomd.mm"
include "mpjaodan.mm"
include "orcd.mm"
include "olcd.mm"
include "readdcld.mm"
include "leloed.mm"
include "mpbid.mm"
include "exp31.mm"
include "ralrimi.mm"
include "nn0ind.mm"
include "ancri.mm"
include "leidd.mm"

theorem wallispilem3
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let vw: setvar w
  assume wallispilem3.1: |- I = ( n e. NN0 |-> S. ( 0 (,) _pi ) ( ( sin ` x ) ^ n ) _d x )

  disjoint n x
  disjoint k m
  disjoint k y
  disjoint m y
  disjoint m n
  disjoint m x
  disjoint m w
  disjoint w y
  disjoint I k
  disjoint I m
  disjoint I w
  disjoint I y
  disjoint N m
  disjoint N w
  disjoint k x
  assert |- ( N e. NN0 -> ( I ` N ) e. RR+ )

  proof
    cN
    cn0
    wcel
    #
    vm
    cv
    #
    cN
    cle
    wbr
    #
    @1
    cI
    cfv
    #
    crp
    wcel
    #
    wi
    #
    vm
    cn0
    wral
    #
    @0
    wa
    cN
    cN
    cle
    wbr
    #
    cN
    cI
    cfv
    #
    crp
    wcel
    #
    @0
    @6
    @1
    vw
    cv
    #
    cle
    wbr
    #
    @4
    wi
    #
    vm
    cn0
    wral
    @1
    cc0
    cle
    wbr
    #
    @4
    wi
    #
    vm
    cn0
    wral
    @1
    vy
    cv
    #
    cle
    wbr
    #
    @4
    wi
    #
    vm
    cn0
    wral
    #
    @1
    @15
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @4
    wi
    #
    vm
    cn0
    wral
    #
    @6
    vw
    vy
    cN
    @10
    cc0
    wceq
    #
    @12
    @14
    vm
    cn0
    @23
    @11
    @13
    @4
    @10
    cc0
    @1
    cle
    breq2
    imbi1d
    ralbidv
    @10
    @15
    wceq
    #
    @12
    @17
    vm
    cn0
    @24
    @11
    @16
    @4
    @10
    @15
    @1
    cle
    breq2
    imbi1d
    ralbidv
    @10
    @19
    wceq
    #
    @12
    @21
    vm
    cn0
    @25
    @11
    @20
    @4
    @10
    @19
    @1
    cle
    breq2
    imbi1d
    ralbidv
    @10
    cN
    wceq
    #
    @12
    @5
    vm
    cn0
    @26
    @11
    @2
    @4
    @10
    cN
    @1
    cle
    breq2
    imbi1d
    ralbidv
    @14
    vm
    cn0
    @1
    cn0
    wcel
    #
    @13
    @4
    @27
    @13
    wa
    #
    @3
    cc0
    cI
    cfv
    #
    crp
    @28
    @1
    cc0
    cI
    @28
    @1
    cc0
    wceq
    #
    @13
    cc0
    @1
    cle
    wbr
    #
    @27
    @13
    simpr
    @27
    @31
    @13
    @1
    nn0ge0
    adantr
    @28
    @1
    cc0
    @27
    @1
    cr
    wcel
    #
    @13
    @1
    nn0re
    #
    adantr
    @28
    0red
    letri3d
    mpbir2and
    fveq2d
    @29
    cpi
    crp
    @29
    cpi
    wceq
    #
    c1
    cI
    cfv
    #
    c2
    wceq
    #
    @1
    c2
    cuz
    cfv
    #
    wcel
    #
    @3
    @1
    c1
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @1
    c2
    cmin
    co
    #
    cI
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    vx
    vn
    cI
    @1
    wallispilem3.1
    wallispilem2
    #
    simp1i
    pirp
    eqeltri
    syl6eqel
    ex
    rgen
    @15
    cn0
    wcel
    #
    @18
    @22
    @47
    @18
    wa
    #
    @21
    vm
    cn0
    @47
    @18
    vm
    @47
    vm
    nfv
    @17
    vm
    cn0
    nfra1
    nfan
    @48
    @27
    @20
    @4
    @48
    @27
    wa
    #
    @20
    wa
    #
    @16
    @4
    @1
    @19
    wceq
    #
    @50
    @18
    @27
    @17
    @47
    @18
    @27
    @20
    simpllr
    @48
    @27
    @20
    simplr
    #
    @17
    vm
    cn0
    rsp
    sylc
    @50
    @51
    @4
    @49
    @51
    @4
    @20
    @49
    @51
    wa
    #
    @1
    c1
    wceq
    #
    @4
    @38
    @54
    @4
    wi
    @53
    @54
    @3
    @35
    crp
    @1
    c1
    cI
    fveq2
    @35
    c2
    crp
    @34
    @36
    @45
    @46
    simp2i
    2rp
    eqeltri
    syl6eqel
    a1i
    @53
    @38
    @4
    @48
    @51
    @38
    @4
    @27
    @48
    @51
    wa
    #
    @38
    wa
    #
    @3
    @43
    crp
    @38
    @44
    @55
    @34
    @36
    @45
    @46
    simp3i
    adantl
    @56
    @40
    @42
    @38
    @40
    crp
    wcel
    @55
    @38
    @39
    @1
    @38
    @39
    @38
    @1
    cn
    wcel
    #
    @39
    cr
    wcel
    #
    @1
    eluz2nn
    #
    @57
    @1
    c1
    @1
    nnre
    #
    @57
    1red
    resubcld
    #
    syl
    @38
    cc0
    c1
    c1
    cmin
    co
    @39
    clt
    1m1e0
    @38
    c1
    @1
    c1
    @38
    1red
    #
    c2
    @1
    eluzelre
    @62
    @38
    @57
    c1
    @1
    clt
    wbr
    @1
    eluz2b2
    simprbi
    ltsub1dd
    syl5eqbrr
    elrpd
    @38
    @1
    @59
    nnrpd
    rpdivcld
    adantl
    @56
    vk
    cv
    #
    @15
    cle
    wbr
    #
    @63
    cI
    cfv
    #
    crp
    wcel
    #
    wi
    #
    vk
    cn0
    wral
    #
    @41
    cn0
    wcel
    #
    wa
    @41
    @15
    cle
    wbr
    #
    @42
    crp
    wcel
    #
    @56
    @68
    @69
    @18
    @68
    @47
    @51
    @38
    @18
    @68
    @17
    @67
    vm
    vk
    cn0
    @1
    @63
    wceq
    #
    @16
    @64
    @4
    @66
    @1
    @63
    @15
    cle
    breq1
    @72
    @3
    @65
    crp
    @1
    @63
    cI
    fveq2
    eleq1d
    imbi12d
    cbvralv
    biimpi
    ad3antlr
    @38
    @69
    @55
    c2
    @1
    uznn0sub
    adantl
    jca
    @56
    @47
    @51
    @38
    @70
    @47
    @18
    @51
    @38
    simplll
    @48
    @51
    @38
    simplr
    @55
    @38
    simpr
    @47
    @51
    @38
    w3a
    #
    @41
    @15
    c1
    cmin
    co
    #
    @15
    cle
    @73
    @41
    @19
    c2
    cmin
    co
    #
    @74
    @73
    @1
    @19
    c2
    cmin
    @47
    @51
    @38
    simp2
    oveq1d
    @73
    @15
    cc
    wcel
    #
    @75
    @74
    wceq
    @73
    @15
    @47
    @51
    @15
    cr
    wcel
    #
    @38
    @15
    nn0re
    #
    3ad2ant1
    #
    recnd
    @76
    @75
    @19
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @74
    @76
    c2
    @80
    @19
    cmin
    c2
    @80
    wceq
    @76
    df-2
    a1i
    oveq2d
    @76
    @15
    c1
    c1
    @76
    id
    @76
    1cnd
    #
    @81
    pnpcan2d
    eqtrd
    syl
    eqtrd
    @73
    @15
    @79
    lem1d
    eqbrtrd
    syl3anc
    @67
    @70
    @71
    wi
    vk
    @41
    cn0
    @63
    @41
    wceq
    #
    @64
    @70
    @66
    @71
    @63
    @41
    @15
    cle
    breq1
    @82
    @65
    @42
    crp
    @63
    @41
    cI
    fveq2
    eleq1d
    imbi12d
    rspccva
    sylc
    rpmulcld
    eqeltrd
    adantllr
    ex
    @53
    @47
    @27
    @51
    @54
    @38
    wo
    #
    @47
    @18
    @27
    @51
    simplll
    @48
    @27
    @51
    simplr
    @49
    @51
    simpr
    @47
    @27
    @51
    w3a
    #
    @1
    c1
    cuz
    cfv
    wcel
    #
    @83
    @84
    @57
    @85
    @84
    @1
    @19
    cn
    @47
    @27
    @51
    simp3
    @47
    @27
    @19
    cn
    wcel
    @51
    @15
    nn0p1nn
    3ad2ant1
    eqeltrd
    @1
    elnnuz
    sylib
    @85
    @54
    @1
    @80
    cuz
    cfv
    #
    wcel
    #
    wo
    @83
    c1
    @1
    uzp1
    @87
    @38
    @54
    @86
    @37
    @1
    @80
    c2
    cuz
    1p1e2
    fveq2i
    eleq2i
    orbi2i
    sylib
    syl
    syl3anc
    mpjaod
    adantlr
    ex
    @50
    @47
    @27
    @20
    @16
    @51
    wo
    #
    @47
    @18
    @27
    @20
    simplll
    @52
    @49
    @20
    simpr
    @47
    @27
    @20
    w3a
    #
    @1
    @19
    clt
    wbr
    #
    @88
    @51
    @89
    @90
    wa
    @47
    @27
    @90
    @88
    @47
    @27
    @20
    @90
    simpl1
    @47
    @27
    @20
    @90
    simpl2
    @89
    @90
    simpr
    @47
    @27
    @90
    w3a
    #
    @16
    @51
    @91
    @30
    @16
    @57
    @47
    @27
    @30
    @16
    @90
    @47
    @30
    wa
    @1
    cc0
    @15
    cle
    @47
    @30
    simpr
    @47
    cc0
    @15
    cle
    wbr
    @30
    @15
    nn0ge0
    adantr
    eqbrtrd
    3ad2antl1
    @91
    @57
    wa
    @47
    @57
    @90
    @16
    @47
    @27
    @90
    @57
    simpl1
    @91
    @57
    simpr
    @47
    @27
    @90
    @57
    simpl3
    @47
    @57
    @90
    w3a
    #
    @16
    @90
    @47
    @57
    @90
    simp3
    #
    @92
    @57
    @15
    cn
    wcel
    #
    @16
    @90
    wb
    @47
    @57
    @90
    simp2
    @92
    @47
    @15
    cc0
    wne
    @94
    @47
    @57
    @90
    simp1
    @92
    @15
    @92
    cc0
    @39
    @15
    @92
    0red
    @57
    @47
    @58
    @90
    @61
    3ad2ant2
    @47
    @57
    @77
    @90
    @78
    3ad2ant1
    #
    @57
    @47
    cc0
    @39
    cle
    wbr
    @90
    @1
    nnm1ge0
    3ad2ant2
    @92
    @39
    @15
    clt
    wbr
    @90
    @93
    @92
    @1
    c1
    @15
    @57
    @47
    @32
    @90
    @60
    3ad2ant2
    @92
    1red
    @95
    ltsubaddd
    mpbird
    lelttrd
    gt0ne0d
    @15
    elnnne0
    sylanbrc
    @1
    @15
    nnleltp1
    syl2anc
    mpbird
    syl3anc
    @27
    @47
    @30
    @57
    wo
    @90
    @27
    @57
    @30
    @27
    @57
    @30
    wo
    @1
    elnn0
    biimpi
    orcomd
    3ad2ant2
    mpjaodan
    orcd
    syl3anc
    @89
    @51
    wa
    @51
    @16
    @89
    @51
    simpr
    olcd
    @89
    @20
    @90
    @51
    wo
    @47
    @27
    @20
    simp3
    @89
    @1
    @19
    @27
    @47
    @32
    @20
    @33
    3ad2ant2
    @89
    @15
    c1
    @47
    @27
    @77
    @20
    @78
    3ad2ant1
    @89
    1red
    readdcld
    leloed
    mpbid
    mpjaodan
    syl3anc
    mpjaod
    exp31
    ralrimi
    ex
    nn0ind
    ancri
    @0
    cN
    cN
    nn0re
    leidd
    @5
    @7
    @9
    wi
    vm
    cN
    cn0
    @1
    cN
    wceq
    #
    @2
    @7
    @4
    @9
    @1
    cN
    cN
    cle
    breq1
    @96
    @3
    @8
    crp
    @1
    cN
    cI
    fveq2
    eleq1d
    imbi12d
    rspccva
    sylc
end
