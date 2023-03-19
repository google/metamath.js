include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "crab.mm"
include "cvv.mm"
include "rabexg.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "syl.mm"
include "unieq.mm"
include "sseq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylan.mm"
include "ex.mm"
include "restuni.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "wel.mm"
include "wex.mm"
include "selpw.mm"
include "wb.mm"
include "eleq2.mm"
include "eluni.mm"
include "syl6bb.mm"
include "adantl.mm"
include "ssel.mm"
include "sseq2i.mm"
include "uniexg.mm"
include "ssexg.mm"
include "ancoms.mm"
include "sylan2b.mm"
include "elrest.mm"
include "syldan.mm"
include "w3a.mm"
include "inss1.mm"
include "sseq1.mm"
include "sselda.mm"
include "3ad2antl3.mm"
include "3adant2.mm"
include "simp12.mm"
include "eleq1.mm"
include "biimpa.mm"
include "3adant3.mm"
include "weq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "vex.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimdv3a.mm"
include "sylbid.mm"
include "com23.mm"
include "com4l.mm"
include "sylcom.mm"
include "com24.mm"
include "impcom.mm"
include "impd.mm"
include "exlimdv.mm"
include "imp.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "pm2.27.mm"
include "elin.mm"
include "cab.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "eleq1a.mm"
include "sylbi.mm"
include "syl6.mm"
include "2a1d.mm"
include "sylanb.mm"
include "3imp.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "abrexex.mm"
include "elpw.mm"
include "sylibr.mm"
include "abrexfi.mm"
include "ad2antlr.mm"
include "elind.mm"
include "ciun.mm"
include "dfss.mm"
include "biimpi.mm"
include "uniiun.mm"
include "ineq2i.mm"
include "iunin2.mm"
include "incom.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtr2i.mm"
include "syl6eq.mm"
include "3ad2ant2.mm"
include "ad2antrl.mm"
include "3adant1.mm"
include "inex1.mm"
include "dfiun2.mm"
include "3eqtr3d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rexlimiv.mm"
include "com3r.mm"
include "mpd.mm"
include "sylbird.mm"
include "syld.mm"
include "ralrimdva.mm"

theorem cmpsublem
  let vt: setvar t
  let cS: class S
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume cmpsub.1: |- X = U. J

  disjoint c d
  disjoint c s
  disjoint c t
  disjoint J c
  disjoint d s
  disjoint d t
  disjoint J d
  disjoint s t
  disjoint J s
  disjoint J t
  disjoint S c
  disjoint S d
  disjoint S s
  disjoint S t
  disjoint X c
  disjoint X d
  disjoint X s
  disjoint X t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint c f
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint c x
  disjoint d x
  disjoint f x
  disjoint S f
  disjoint s x
  disjoint t x
  disjoint u x
  disjoint S u
  disjoint v x
  disjoint S v
  disjoint w x
  disjoint S w
  disjoint x z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X f
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( J e. Top /\ S C_ X ) -> ( A. c e. ~P J ( S C_ U. c -> E. d e. ( ~P c i^i Fin ) S C_ U. d ) -> A. s e. ~P ( J |`t S ) ( U. ( J |`t S ) = U. s -> E. t e. ( ~P s i^i Fin ) U. ( J |`t S ) = U. t ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    vc
    cv
    #
    cuni
    #
    wss
    #
    cS
    vd
    cv
    #
    cuni
    #
    wss
    #
    vd
    @3
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vc
    cJ
    cpw
    #
    wral
    #
    cJ
    cS
    crest
    co
    #
    cuni
    #
    vs
    cv
    #
    cuni
    #
    wceq
    #
    @16
    vt
    cv
    #
    cuni
    #
    wceq
    #
    vt
    @17
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vs
    @15
    cpw
    #
    @2
    @17
    @27
    wcel
    #
    wa
    #
    @14
    cS
    vy
    cv
    #
    cS
    cin
    #
    @17
    wcel
    #
    vy
    cJ
    crab
    #
    cuni
    #
    wss
    #
    @8
    vd
    @33
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    @26
    @29
    @14
    @39
    @29
    @33
    @13
    wcel
    #
    @14
    @39
    @29
    @33
    cvv
    wcel
    #
    @40
    @0
    @41
    @1
    @28
    @32
    vy
    cJ
    ctop
    rabexg
    ad2antrr
    @41
    @40
    @33
    cJ
    wss
    @32
    vy
    cJ
    ssrab2
    @33
    cJ
    cvv
    elpwg
    mpbiri
    syl
    @12
    @39
    vc
    @33
    @13
    @3
    @33
    wceq
    #
    @5
    @35
    @11
    @38
    @42
    @4
    @34
    cS
    @3
    @33
    unieq
    sseq2d
    @42
    @8
    vd
    @10
    @37
    @42
    @9
    @36
    cfn
    @3
    @33
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcva
    sylan
    ex
    @29
    @19
    @39
    @25
    @29
    @19
    cS
    @18
    wceq
    #
    @39
    @25
    wi
    #
    @29
    cS
    @16
    @18
    @2
    cS
    @16
    wceq
    #
    @28
    cS
    cJ
    cX
    cmpsub.1
    restuni
    adantr
    #
    eqeq1d
    @29
    @43
    @44
    @29
    @43
    wa
    #
    @35
    @44
    @47
    vt
    cS
    @34
    @47
    @20
    cS
    wcel
    #
    vt
    vv
    wel
    #
    vv
    cv
    #
    @33
    wcel
    #
    wa
    #
    vv
    wex
    #
    @20
    @34
    wcel
    @29
    @43
    @48
    @53
    wi
    #
    @28
    @2
    @17
    @15
    wss
    #
    @43
    @54
    wi
    vs
    @15
    selpw
    @2
    @55
    wa
    #
    @43
    @54
    @56
    @43
    wa
    @48
    vt
    vu
    wel
    #
    vu
    vs
    wel
    #
    wa
    #
    vu
    wex
    #
    @53
    @43
    @48
    @60
    wb
    @56
    @43
    @48
    @20
    @18
    wcel
    @60
    cS
    @18
    @20
    eleq2
    vu
    @20
    @17
    eluni
    syl6bb
    adantl
    @56
    @60
    @53
    wi
    @43
    @56
    @59
    @53
    vu
    @56
    @57
    @58
    @53
    @55
    @2
    @57
    @58
    @53
    wi
    wi
    @55
    @58
    @57
    @2
    @53
    @55
    @58
    vu
    cv
    #
    @15
    wcel
    #
    @57
    @2
    @53
    wi
    wi
    @17
    @15
    @61
    ssel
    @2
    @58
    @62
    @57
    @53
    @2
    @62
    @58
    @57
    @53
    wi
    #
    @2
    @62
    @61
    vw
    cv
    #
    cS
    cin
    #
    wceq
    #
    vw
    cJ
    wrex
    #
    @58
    @63
    wi
    #
    @0
    @1
    cS
    cvv
    wcel
    #
    @62
    @67
    wb
    @1
    @0
    cS
    cJ
    cuni
    #
    wss
    #
    @69
    cX
    @70
    cS
    cmpsub.1
    sseq2i
    @0
    @70
    cvv
    wcel
    #
    @71
    @69
    cJ
    ctop
    uniexg
    @71
    @72
    @69
    cS
    @70
    cvv
    ssexg
    ancoms
    sylan
    sylan2b
    vw
    @61
    cS
    cJ
    ctop
    cvv
    elrest
    syldan
    @2
    @66
    @68
    vw
    cJ
    @2
    @64
    cJ
    wcel
    #
    @66
    w3a
    #
    @58
    @57
    @53
    @74
    @58
    @57
    w3a
    #
    vt
    vw
    wel
    #
    @64
    @33
    wcel
    #
    @53
    @74
    @57
    @76
    @58
    @66
    @2
    @57
    @76
    @73
    @66
    @61
    @64
    @20
    @66
    @61
    @64
    wss
    @65
    @64
    wss
    @64
    cS
    inss1
    @61
    @65
    @64
    sseq1
    mpbiri
    sselda
    3ad2antl3
    3adant2
    @75
    @73
    @65
    @17
    wcel
    #
    @77
    @2
    @73
    @66
    @58
    @57
    simp12
    @74
    @58
    @78
    @57
    @66
    @2
    @58
    @78
    @73
    @66
    @58
    @78
    @61
    @65
    @17
    eleq1
    biimpa
    3ad2antl3
    3adant3
    @32
    @78
    vy
    @64
    cJ
    vy
    vw
    weq
    @31
    @65
    @17
    @30
    @64
    cS
    ineq1
    eleq1d
    elrab
    sylanbrc
    @52
    @76
    @77
    wa
    vv
    @64
    vw
    vex
    vv
    vw
    weq
    @49
    @76
    @51
    @77
    @50
    @64
    @20
    eleq2
    @50
    @64
    @33
    eleq1
    anbi12d
    spcev
    syl2anc
    3exp
    rexlimdv3a
    sylbid
    com23
    com4l
    sylcom
    com24
    impcom
    impd
    exlimdv
    adantr
    sylbid
    ex
    sylan2b
    imp
    vv
    @20
    @33
    eluni
    syl6ibr
    ssrdv
    @35
    @39
    @47
    @25
    @35
    @39
    @38
    @47
    @25
    wi
    #
    @35
    @38
    pm2.27
    @8
    @79
    vd
    @37
    @6
    @37
    wcel
    @6
    @36
    wcel
    #
    @6
    cfn
    wcel
    #
    wa
    #
    @8
    @79
    wi
    @6
    @36
    cfn
    elin
    @82
    @8
    @47
    @25
    @82
    @8
    @47
    w3a
    #
    vx
    cv
    #
    vz
    cv
    #
    cS
    cin
    #
    wceq
    #
    vz
    @6
    wrex
    #
    vx
    cab
    #
    @24
    wcel
    @16
    @89
    cuni
    #
    wceq
    #
    @25
    @83
    @23
    cfn
    @89
    @83
    @89
    @17
    wss
    @89
    @23
    wcel
    @83
    vt
    @89
    @17
    @20
    @89
    wcel
    @20
    @86
    wceq
    #
    vz
    @6
    wrex
    #
    @83
    vt
    vs
    wel
    #
    @88
    @93
    vx
    @20
    vt
    vex
    vx
    vt
    weq
    @87
    @92
    vz
    @6
    @84
    @20
    @86
    eqeq1
    rexbidv
    elab
    @83
    @92
    @94
    vz
    @6
    @82
    @8
    @47
    vz
    vd
    wel
    #
    @92
    @94
    wi
    #
    wi
    #
    @80
    @6
    @33
    wss
    #
    @81
    @8
    @47
    @97
    wi
    wi
    #
    vd
    @33
    selpw
    @98
    @99
    @81
    @98
    @97
    @8
    @47
    @98
    @95
    @85
    @33
    wcel
    #
    @96
    @6
    @33
    @85
    ssel
    @100
    @85
    cJ
    wcel
    #
    @86
    @17
    wcel
    #
    wa
    @96
    @32
    @102
    vy
    @85
    cJ
    vy
    vz
    weq
    @31
    @86
    @17
    @30
    @85
    cS
    ineq1
    eleq1d
    elrab
    @102
    @96
    @101
    @86
    @17
    @20
    eleq1a
    adantl
    sylbi
    syl6
    2a1d
    adantr
    sylanb
    3imp
    rexlimdv
    syl5bi
    ssrdv
    @89
    @17
    vz
    vx
    @6
    @86
    vd
    vex
    abrexex
    elpw
    sylibr
    @82
    @8
    @89
    cfn
    wcel
    #
    @47
    @81
    @103
    @80
    @8
    vz
    vx
    @6
    @86
    abrexfi
    ad2antlr
    3adant3
    elind
    @83
    cS
    vz
    @6
    @86
    ciun
    #
    @16
    @90
    @8
    @82
    cS
    @104
    wceq
    @47
    @8
    cS
    cS
    @7
    cin
    #
    @104
    @8
    cS
    @105
    wceq
    cS
    @7
    dfss
    biimpi
    @105
    cS
    vz
    @6
    @85
    ciun
    #
    cin
    vz
    @6
    cS
    @85
    cin
    #
    ciun
    @104
    @7
    @106
    cS
    vz
    @6
    uniiun
    ineq2i
    vz
    @6
    cS
    @85
    iunin2
    vz
    @6
    @107
    @86
    @107
    @86
    wceq
    @95
    cS
    @85
    incom
    a1i
    iuneq2i
    3eqtr2i
    syl6eq
    3ad2ant2
    @8
    @47
    @45
    @82
    @29
    @45
    @8
    @43
    @46
    ad2antrl
    3adant1
    @104
    @90
    wceq
    @83
    vz
    vx
    @6
    @86
    @85
    cS
    vz
    vex
    inex1
    dfiun2
    a1i
    3eqtr3d
    @22
    @91
    vt
    @89
    @24
    @20
    @89
    wceq
    @21
    @90
    @16
    @20
    @89
    unieq
    eqeq2d
    rspcev
    syl2anc
    3exp
    sylbi
    rexlimiv
    syl6
    com3r
    mpd
    ex
    sylbird
    com23
    syld
    ralrimdva
end
