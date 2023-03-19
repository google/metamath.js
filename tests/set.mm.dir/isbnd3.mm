include "cbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cxp.mm"
include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "bndmet.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "wral.mm"
include "0re.mm"
include "ne0ii.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "metf.mm"
include "ffn.mm"
include "syl.mm"
include "ad2antrr.mm"
include "cdm.mm"
include "fdm.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "adantr.mm"
include "dm0rn0.mm"
include "sylib.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "cbl.mm"
include "crp.mm"
include "cxmt.mm"
include "isbnd2.mm"
include "simprbi.mm"
include "wi.mm"
include "c2.mm"
include "cmul.mm"
include "2re.mm"
include "simprlr.mm"
include "rpred.mm"
include "remulcl.mm"
include "cle.mm"
include "wbr.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "metge0.mm"
include "caddc.mm"
include "simprll.mm"
include "readdcld.mm"
include "mettri2.mm"
include "syl13anc.mm"
include "clt.mm"
include "simplrr.mm"
include "eleqtrd.mm"
include "cxr.mm"
include "wb.mm"
include "metxmet.mm"
include "rpxr.mm"
include "ad2antlr.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "lt2addd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "lelttrd.mm"
include "ltled.mm"
include "w3a.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "oveq2.mm"
include "feq3d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "pm2.61dane.mm"
include "jca.mm"
include "c1.mm"
include "simpllr.mm"
include "simpr.mm"
include "met0.mm"
include "simplr.mm"
include "fovrnd.mm"
include "simp3d.mm"
include "eqbrtrrd.mm"
include "ge0p1rpd.mm"
include "crab.mm"
include "fovrn.mm"
include "3expa.mm"
include "adantlll.mm"
include "simp1d.mm"
include "peano2re.mm"
include "ltp1d.mm"
include "rabid2.mm"
include "sylibr.mm"
include "rexrd.mm"
include "blval.mm"
include "eqtr4d.mm"
include "eqeq2d.mm"
include "isbnd.mm"
include "r19.29an.mm"
include "impbii.mm"

theorem isbnd3
  let vx: setvar x
  let cM: class M
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cP: class P
  let cR: class R
  let cS: class S
  let cY: class Y

  disjoint M x
  disjoint X x
  disjoint d m
  disjoint d r
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint M d
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint M r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint N d
  disjoint N r
  disjoint N y
  disjoint P d
  disjoint P r
  disjoint P y
  disjoint X d
  disjoint X m
  disjoint X r
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint R r
  disjoint R x
  disjoint S r
  disjoint S x
  disjoint Y d
  disjoint Y r
  disjoint Y x
  disjoint Y y
  assert |- ( M e. ( Bnd ` X ) <-> ( M e. ( Met ` X ) /\ E. x e. RR M : ( X X. X ) --> ( 0 [,] x ) ) )

  proof
    cM
    cX
    cbnd
    cfv
    wcel
    #
    cM
    cX
    cme
    cfv
    wcel
    #
    cX
    cX
    cxp
    #
    cc0
    vx
    cv
    #
    cicc
    co
    #
    cM
    wf
    #
    vx
    cr
    wrex
    #
    wa
    @0
    @1
    @6
    cM
    cX
    bndmet
    #
    @0
    @6
    cX
    c0
    @0
    cX
    c0
    wceq
    #
    wa
    #
    cr
    c0
    wne
    @5
    vx
    cr
    wral
    @6
    cc0
    cr
    0re
    ne0ii
    @9
    @5
    vx
    cr
    @9
    @3
    cr
    wcel
    #
    wa
    #
    cM
    @2
    wfn
    #
    cM
    crn
    #
    @4
    wss
    @5
    @0
    @12
    @8
    @10
    @0
    @1
    @12
    @7
    @1
    @2
    cr
    cM
    wf
    #
    @12
    cM
    cX
    metf
    #
    @2
    cr
    cM
    ffn
    syl
    #
    syl
    ad2antrr
    @11
    @13
    c0
    @4
    @11
    cM
    cdm
    #
    c0
    wceq
    #
    @13
    c0
    wceq
    @9
    @18
    @10
    @0
    @8
    @17
    @2
    c0
    @0
    @14
    @17
    @2
    wceq
    @0
    @1
    @14
    @7
    @15
    syl
    @2
    cr
    cM
    fdm
    syl
    @8
    @2
    cX
    c0
    cxp
    c0
    cX
    c0
    cX
    xpeq2
    cX
    xp0
    syl6eq
    sylan9eq
    adantr
    cM
    dm0rn0
    sylib
    @4
    0ss
    syl6eqss
    @2
    @4
    cM
    df-f
    sylanbrc
    ralrimiva
    @5
    vx
    cr
    r19.2z
    sylancr
    @0
    cX
    c0
    wne
    #
    wa
    #
    cX
    vy
    cv
    #
    vr
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vy
    cX
    wrex
    #
    @6
    @20
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @27
    vy
    cM
    cX
    vr
    isbnd2
    simprbi
    @0
    @27
    @6
    wi
    #
    @19
    @0
    @1
    @29
    @7
    @1
    @25
    @6
    vy
    vr
    cX
    crp
    @1
    @21
    cX
    wcel
    #
    @22
    crp
    wcel
    #
    wa
    #
    @25
    @6
    @1
    @32
    @25
    wa
    #
    wa
    #
    c2
    @22
    cmul
    co
    #
    cr
    wcel
    #
    @2
    cc0
    @35
    cicc
    co
    #
    cM
    wf
    #
    @6
    @34
    c2
    cr
    wcel
    @22
    cr
    wcel
    #
    @36
    2re
    @34
    @22
    @1
    @30
    @31
    @25
    simprlr
    rpred
    #
    c2
    @22
    remulcl
    sylancr
    #
    @34
    @12
    @3
    vz
    cv
    #
    cM
    co
    #
    @37
    wcel
    #
    vz
    cX
    wral
    vx
    cX
    wral
    @38
    @1
    @12
    @33
    @16
    adantr
    @34
    @44
    vx
    vz
    cX
    cX
    @34
    @3
    cX
    wcel
    #
    @42
    cX
    wcel
    #
    wa
    #
    wa
    #
    @44
    @43
    cr
    wcel
    #
    cc0
    @43
    cle
    wbr
    #
    @43
    @35
    cle
    wbr
    #
    @48
    @1
    @45
    @46
    @49
    @1
    @33
    @47
    simpll
    #
    @34
    @45
    @46
    simprl
    #
    @34
    @45
    @46
    simprr
    #
    @3
    @42
    cM
    cX
    metcl
    syl3anc
    #
    @48
    @1
    @45
    @46
    @50
    @52
    @53
    @54
    @3
    @42
    cM
    cX
    metge0
    syl3anc
    @48
    @43
    @35
    @55
    @34
    @36
    @47
    @41
    adantr
    #
    @48
    @43
    @21
    @3
    cM
    co
    #
    @21
    @42
    cM
    co
    #
    caddc
    co
    #
    @35
    @55
    @48
    @57
    @58
    @48
    @1
    @30
    @45
    @57
    cr
    wcel
    @52
    @34
    @30
    @47
    @1
    @30
    @31
    @25
    simprll
    adantr
    #
    @53
    @21
    @3
    cM
    cX
    metcl
    syl3anc
    #
    @48
    @1
    @30
    @46
    @58
    cr
    wcel
    #
    @52
    @60
    @54
    @21
    @42
    cM
    cX
    metcl
    syl3anc
    #
    readdcld
    @56
    @48
    @1
    @30
    @45
    @46
    @43
    @59
    cle
    wbr
    @52
    @60
    @53
    @54
    @3
    @42
    @21
    cM
    cX
    mettri2
    syl13anc
    @48
    @59
    @22
    @22
    caddc
    co
    @35
    clt
    @48
    @57
    @58
    @22
    @22
    @61
    @63
    @34
    @39
    @47
    @40
    adantr
    #
    @64
    @48
    @3
    @24
    wcel
    #
    @57
    @22
    clt
    wbr
    #
    @48
    @3
    cX
    @24
    @53
    @1
    @32
    @25
    @47
    simplrr
    #
    eleqtrd
    @48
    @28
    @22
    cxr
    wcel
    #
    @30
    @45
    @65
    @66
    wb
    @48
    @1
    @28
    @52
    cM
    cX
    metxmet
    #
    syl
    #
    @33
    @68
    @1
    @47
    @31
    @68
    @30
    @25
    @22
    rpxr
    ad2antlr
    ad2antlr
    #
    @60
    @53
    @3
    cM
    @21
    @22
    cX
    elbl2
    syl22anc
    mpbid
    @48
    @42
    @24
    wcel
    #
    @58
    @22
    clt
    wbr
    #
    @48
    @42
    cX
    @24
    @54
    @67
    eleqtrd
    @48
    @28
    @68
    @30
    @46
    @72
    @73
    wb
    @70
    @71
    @60
    @54
    @42
    cM
    @21
    @22
    cX
    elbl2
    syl22anc
    mpbid
    lt2addd
    @48
    @22
    @48
    @22
    @64
    recnd
    2timesd
    breqtrrd
    lelttrd
    ltled
    @48
    cc0
    cr
    wcel
    #
    @36
    @44
    @49
    @50
    @51
    w3a
    wb
    0re
    @56
    cc0
    @35
    @43
    elicc2
    sylancr
    mpbir3and
    ralrimivva
    vx
    vz
    cX
    cX
    @37
    cM
    ffnov
    sylanbrc
    @5
    @38
    vx
    @35
    cr
    @3
    @35
    wceq
    @4
    @37
    cM
    @2
    @3
    @35
    cc0
    cicc
    oveq2
    feq3d
    rspcev
    syl2anc
    expr
    rexlimdvva
    syl
    adantr
    mpd
    pm2.61dane
    jca
    @1
    @5
    @0
    vx
    cr
    @1
    @10
    wa
    #
    @5
    wa
    #
    @1
    @26
    vy
    cX
    wral
    @0
    @1
    @10
    @5
    simpll
    #
    @76
    @26
    vy
    cX
    @76
    @30
    wa
    #
    @3
    c1
    caddc
    co
    #
    crp
    wcel
    cX
    @21
    @79
    @23
    co
    #
    wceq
    #
    @26
    @78
    @3
    @1
    @10
    @5
    @30
    simpllr
    #
    @78
    @21
    @21
    cM
    co
    #
    cc0
    @3
    cle
    @78
    @1
    @30
    @83
    cc0
    wceq
    @76
    @1
    @30
    @77
    adantr
    #
    @76
    @30
    simpr
    #
    @21
    cM
    cX
    met0
    syl2anc
    @78
    @83
    cr
    wcel
    #
    cc0
    @83
    cle
    wbr
    #
    @83
    @3
    cle
    wbr
    #
    @78
    @83
    @4
    wcel
    #
    @86
    @87
    @88
    w3a
    #
    @78
    @21
    @21
    @4
    cX
    cX
    cM
    @75
    @5
    @30
    simplr
    @85
    @85
    fovrnd
    @78
    @74
    @10
    @89
    @90
    wb
    0re
    @82
    cc0
    @3
    @83
    elicc2
    sylancr
    mpbid
    simp3d
    eqbrtrrd
    ge0p1rpd
    @78
    cX
    @58
    @79
    clt
    wbr
    #
    vz
    cX
    crab
    #
    @80
    @78
    @91
    vz
    cX
    wral
    cX
    @92
    wceq
    @78
    @91
    vz
    cX
    @78
    @46
    wa
    #
    @58
    @3
    @79
    @93
    @62
    cc0
    @58
    cle
    wbr
    #
    @58
    @3
    cle
    wbr
    #
    @93
    @58
    @4
    wcel
    #
    @62
    @94
    @95
    w3a
    #
    @5
    @30
    @46
    @96
    @75
    @5
    @30
    @46
    @96
    @21
    @42
    @4
    cX
    cX
    cM
    fovrn
    3expa
    adantlll
    @78
    @96
    @97
    wb
    #
    @46
    @78
    @74
    @10
    @98
    0re
    @82
    cc0
    @3
    @58
    elicc2
    sylancr
    adantr
    mpbid
    #
    simp1d
    @78
    @10
    @46
    @82
    adantr
    #
    @78
    @79
    cr
    wcel
    #
    @46
    @78
    @10
    @101
    @82
    @3
    peano2re
    syl
    #
    adantr
    @93
    @62
    @94
    @95
    @99
    simp3d
    @93
    @3
    @100
    ltp1d
    lelttrd
    ralrimiva
    @91
    vz
    cX
    rabid2
    sylibr
    @78
    @28
    @30
    @79
    cxr
    wcel
    @80
    @92
    wceq
    @78
    @1
    @28
    @84
    @69
    syl
    @85
    @78
    @79
    @102
    rexrd
    vz
    cM
    @21
    @79
    cX
    blval
    syl3anc
    eqtr4d
    @25
    @81
    vr
    @79
    crp
    @22
    @79
    wceq
    @24
    @80
    cX
    @22
    @79
    @21
    @23
    oveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    vy
    cM
    cX
    vr
    isbnd
    sylanbrc
    r19.29an
    impbii
end
