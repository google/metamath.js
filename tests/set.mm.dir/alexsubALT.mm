include "ccmp.mm"
include "wcel.mm"
include "cv.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "wceq.mm"
include "cuni.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "alexsubALTlem1.mm"
include "alexsubALTlem4.mm"
include "ctop.mm"
include "wss.mm"
include "selpw.mm"
include "w3a.mm"
include "crab.mm"
include "wel.mm"
include "wb.mm"
include "eleq2.mm"
include "3ad2ant3.mm"
include "eluni.mm"
include "ssel.mm"
include "tg2.mm"
include "ex.mm"
include "syl6bi.mm"
include "sylan9r.mm"
include "3impia.mm"
include "sseq2.mm"
include "rspcev.mm"
include "anim2d.mm"
include "reximdv.mm"
include "syld.mm"
include "3expia.mm"
include "com23.mm"
include "impd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3adant3.mm"
include "sylbid.mm"
include "elunii.mm"
include "expcom.mm"
include "biimprd.mm"
include "syl9r.mm"
include "rexlimdva.mm"
include "rexlimdvw.mm"
include "impbid.mm"
include "elunirab.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "ssrab2.mm"
include "fvex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5com.mm"
include "elfpw.mm"
include "wf.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "ac6sfi.mm"
include "syl5.mm"
include "adantl.mm"
include "crn.mm"
include "simprll.mm"
include "frn.mm"
include "syl.mm"
include "cdom.mm"
include "wbr.mm"
include "simplr.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "fodomfi.mm"
include "syl2anc.mm"
include "domfi.mm"
include "jca.mm"
include "elin.mm"
include "vex.mm"
include "anbi1i.mm"
include "bitr2i.mm"
include "simprr.mm"
include "ciun.mm"
include "uniiun.mm"
include "simprlr.mm"
include "ss2iun.mm"
include "syl5eqss.mm"
include "fniunfv.mm"
include "3syl.mm"
include "sseqtrd.mm"
include "eqsstrd.mm"
include "simpll2.mm"
include "sstrd.mm"
include "uniss.mm"
include "syl6sseqr.mm"
include "eqssd.mm"
include "exp32.mm"
include "rexlimdv.mm"
include "3exp.mm"
include "com34.mm"
include "syl7bi.mm"
include "ralrimdv.mm"
include "ctb.mm"
include "fibas.mm"
include "tgcl.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "jctild.mm"
include "iscmp.mm"
include "syl6ibr.mm"
include "imp.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem alexsubALT
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume alexsubALT.1: |- X = U. J

  disjoint c d
  disjoint c x
  disjoint J c
  disjoint d x
  disjoint J d
  disjoint J x
  disjoint X c
  disjoint X d
  disjoint X x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d m
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( J e. Comp <-> E. x ( J = ( topGen ` ( fi ` x ) ) /\ A. c e. ~P x ( X = U. c -> E. d e. ( ~P c i^i Fin ) X = U. d ) ) )

  proof
    cJ
    ccmp
    wcel
    #
    cJ
    vx
    cv
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    #
    cX
    vc
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vd
    cv
    #
    cuni
    #
    wceq
    #
    vd
    @5
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
    @1
    cpw
    wral
    #
    wa
    #
    vx
    wex
    vx
    cJ
    cX
    vc
    vd
    alexsubALT.1
    alexsubALTlem1
    @16
    @0
    vx
    @4
    @15
    @0
    @4
    @15
    cX
    va
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vb
    cv
    #
    cuni
    #
    wceq
    #
    vb
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
    va
    @2
    cpw
    #
    wral
    #
    @0
    vx
    cJ
    cX
    va
    vb
    vc
    vd
    alexsubALT.1
    alexsubALTlem4
    @4
    @28
    cJ
    ctop
    wcel
    #
    @14
    vc
    cJ
    cpw
    #
    wral
    #
    wa
    @0
    @4
    @28
    @31
    @29
    @4
    @28
    @14
    vc
    @30
    @5
    @30
    wcel
    @5
    cJ
    wss
    #
    @4
    @28
    @14
    vc
    cJ
    selpw
    @4
    @32
    @28
    @14
    @4
    @32
    @7
    @28
    @13
    @4
    @32
    @7
    @28
    @13
    wi
    @4
    @32
    @7
    w3a
    #
    @28
    @22
    vb
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    vz
    @5
    wrex
    #
    vy
    @2
    crab
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @13
    @33
    cX
    @38
    cuni
    #
    wceq
    #
    @28
    @41
    @33
    vt
    cX
    @42
    @33
    vt
    cv
    #
    cX
    wcel
    #
    vt
    vy
    wel
    #
    @37
    wa
    #
    vy
    @2
    wrex
    #
    @44
    @42
    wcel
    @33
    @45
    @48
    @33
    @45
    @44
    @6
    wcel
    #
    @48
    @7
    @4
    @45
    @49
    wb
    @32
    cX
    @6
    @44
    eleq2
    3ad2ant3
    #
    @4
    @32
    @49
    @48
    wi
    @7
    @49
    vt
    vw
    wel
    #
    vw
    vc
    wel
    #
    wa
    #
    vw
    wex
    @4
    @32
    wa
    #
    @48
    vw
    @44
    @5
    eluni
    @54
    @53
    @48
    vw
    @54
    @51
    @52
    @48
    @54
    @52
    @51
    @48
    @4
    @32
    @52
    @51
    @48
    wi
    @4
    @32
    @52
    w3a
    #
    @51
    @46
    @34
    vw
    cv
    #
    wss
    #
    wa
    #
    vy
    @2
    wrex
    #
    @48
    @4
    @32
    @52
    @51
    @59
    wi
    #
    @32
    @52
    @56
    cJ
    wcel
    #
    @4
    @60
    @5
    cJ
    @56
    ssel
    @4
    @61
    @56
    @3
    wcel
    #
    @60
    cJ
    @3
    @56
    eleq2
    @62
    @51
    @59
    vy
    @56
    @2
    @44
    tg2
    ex
    syl6bi
    sylan9r
    3impia
    @55
    @58
    @47
    vy
    @2
    @55
    @57
    @37
    @46
    @52
    @4
    @57
    @37
    wi
    @32
    @52
    @57
    @37
    @36
    @57
    vz
    @56
    @5
    @35
    @56
    @34
    sseq2
    rspcev
    ex
    3ad2ant3
    anim2d
    reximdv
    syld
    3expia
    com23
    impd
    exlimdv
    syl5bi
    3adant3
    sylbid
    @33
    @47
    @45
    vy
    @2
    @33
    @46
    @37
    @45
    @33
    @37
    @46
    @45
    @33
    @36
    @46
    @45
    wi
    vz
    @5
    @36
    @46
    vt
    vz
    wel
    #
    @33
    vz
    vc
    wel
    #
    wa
    @45
    @34
    @35
    @44
    ssel
    @64
    @63
    @49
    @33
    @45
    @63
    @64
    @49
    @44
    @35
    @5
    elunii
    expcom
    @33
    @45
    @49
    @50
    biimprd
    sylan9r
    syl9r
    rexlimdva
    com23
    impd
    rexlimdvw
    impbid
    @37
    vy
    @44
    @2
    elunirab
    syl6bbr
    eqrdv
    @38
    @27
    wcel
    #
    @28
    @43
    @41
    wi
    #
    wi
    @65
    @38
    @2
    wss
    @37
    vy
    @2
    ssrab2
    @38
    @2
    @1
    cfi
    fvex
    elpw2
    mpbir
    @26
    @66
    va
    @38
    @27
    @17
    @38
    wceq
    #
    @19
    @43
    @25
    @41
    @67
    @18
    @42
    cX
    @17
    @38
    unieq
    eqeq2d
    @67
    @22
    vb
    @24
    @40
    @67
    @23
    @39
    cfn
    @17
    @38
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcv
    ax-mp
    syl5com
    @33
    @22
    @13
    vb
    @40
    @20
    @40
    wcel
    @20
    @38
    wss
    #
    @20
    cfn
    wcel
    #
    wa
    @33
    @22
    @13
    wi
    #
    @20
    @38
    elfpw
    @33
    @68
    @69
    @70
    @33
    @69
    @68
    @70
    @33
    @69
    @68
    @70
    wi
    @33
    @69
    wa
    #
    @68
    @20
    @5
    vf
    cv
    #
    wf
    #
    @44
    @44
    @72
    cfv
    #
    wss
    #
    vt
    @20
    wral
    #
    wa
    #
    vf
    wex
    #
    @70
    @69
    @68
    @78
    wi
    @33
    @68
    @44
    @35
    wss
    #
    vz
    @5
    wrex
    #
    vt
    @20
    wral
    #
    @69
    @78
    @68
    @80
    vt
    @20
    @68
    vt
    vb
    wel
    @44
    @38
    wcel
    #
    @80
    @20
    @38
    @44
    ssel
    @82
    @44
    @2
    wcel
    @80
    @37
    @80
    vy
    @44
    @2
    @34
    @44
    wceq
    @36
    @79
    vz
    @5
    @34
    @44
    @35
    sseq1
    rexbidv
    elrab
    simprbi
    syl6
    ralrimiv
    @69
    @81
    @78
    @79
    @75
    vt
    vz
    @20
    @5
    vf
    @35
    @74
    @44
    sseq2
    ac6sfi
    ex
    syl5
    adantl
    @71
    @77
    @70
    vf
    @71
    @77
    @22
    @13
    @71
    @77
    @22
    wa
    #
    wa
    #
    @72
    crn
    #
    @12
    wcel
    #
    cX
    @85
    cuni
    #
    wceq
    #
    @13
    @84
    @85
    @5
    wss
    #
    @85
    cfn
    wcel
    #
    wa
    #
    @86
    @84
    @89
    @90
    @84
    @73
    @89
    @71
    @73
    @76
    @22
    simprll
    #
    @20
    @5
    @72
    frn
    syl
    #
    @84
    @69
    @85
    @20
    cdom
    wbr
    #
    @90
    @33
    @69
    @83
    simplr
    #
    @84
    @69
    @20
    @85
    @72
    wfo
    #
    @94
    @95
    @77
    @96
    @71
    @22
    @73
    @96
    @76
    @73
    @72
    @20
    wfn
    #
    @96
    @20
    @5
    @72
    ffn
    #
    @20
    @72
    dffn4
    sylib
    adantr
    ad2antrl
    @20
    @85
    @72
    fodomfi
    syl2anc
    @20
    @85
    domfi
    syl2anc
    jca
    @86
    @85
    @11
    wcel
    #
    @90
    wa
    @91
    @85
    @11
    cfn
    elin
    @99
    @89
    @90
    @85
    @5
    vc
    vex
    elpw2
    anbi1i
    bitr2i
    sylib
    @84
    cX
    @87
    @84
    cX
    @21
    @87
    @71
    @77
    @22
    simprr
    @84
    @21
    vt
    @20
    @74
    ciun
    #
    @87
    @84
    @21
    vt
    @20
    @44
    ciun
    #
    @100
    vt
    @20
    uniiun
    @84
    @76
    @101
    @100
    wss
    @71
    @73
    @76
    @22
    simprlr
    vt
    @20
    @44
    @74
    ss2iun
    syl
    syl5eqss
    @84
    @73
    @97
    @100
    @87
    wceq
    @92
    @98
    vt
    @20
    @72
    fniunfv
    3syl
    sseqtrd
    eqsstrd
    @84
    @85
    cJ
    wss
    #
    @87
    cX
    wss
    @84
    @85
    @5
    cJ
    @93
    @4
    @32
    @7
    @69
    @83
    simpll2
    sstrd
    @102
    @87
    cJ
    cuni
    cX
    @85
    cJ
    uniss
    alexsubALT.1
    syl6sseqr
    syl
    eqssd
    @10
    @88
    vd
    @85
    @12
    @8
    @85
    wceq
    @9
    @87
    cX
    @8
    @85
    unieq
    eqeq2d
    rspcev
    syl2anc
    exp32
    exlimdv
    syld
    ex
    com23
    impd
    syl5bi
    rexlimdv
    syld
    3exp
    com34
    com23
    syl7bi
    ralrimdv
    @4
    @29
    @3
    ctop
    wcel
    #
    @2
    ctb
    wcel
    @103
    @1
    fibas
    @2
    tgcl
    ax-mp
    cJ
    @3
    ctop
    eleq1
    mpbiri
    jctild
    vc
    vd
    cJ
    cX
    alexsubALT.1
    iscmp
    syl6ibr
    syld
    imp
    exlimiv
    impbii
end
