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
include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "wa.mm"
include "wss.mm"
include "crab.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "crpss.mm"
include "wor.mm"
include "wal.mm"
include "wpss.mm"
include "ssel.mm"
include "wo.mm"
include "elun.mm"
include "weq.mm"
include "sseq2.mm"
include "pweq.mm"
include "ineq1d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "velsn.mm"
include "orbi12i.mm"
include "bitri.mm"
include "elpwi.mm"
include "adantr.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sylbi.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "unissb.mm"
include "sylibr.mm"
include "ad2antlr.mm"
include "vuniex.mm"
include "elpw.mm"
include "uni0b.mm"
include "notbii.mm"
include "wne.mm"
include "disjssun.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "wex.mm"
include "n0.mm"
include "elin.mm"
include "anbi2i.mm"
include "simprrl.mm"
include "simpl.mm"
include "ssuni.mm"
include "syl2anc.mm"
include "exlimiv.mm"
include "ad2antrl.mm"
include "syl5bi.mm"
include "imp.mm"
include "elfpw.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "necon3bi.mm"
include "simplrr.mm"
include "simprlr.mm"
include "simprr.mm"
include "finsschain.mm"
include "syl22anc.mm"
include "expr.mm"
include "0elpw.mm"
include "0fin.mm"
include "mpbir2an.mm"
include "eqeq2d.mm"
include "notbid.mm"
include "rspccv.mm"
include "mpi.mm"
include "vex.mm"
include "syl5bir.mm"
include "expd.mm"
include "com23.mm"
include "ad2antll.mm"
include "a1i.mm"
include "ss0.mm"
include "syl6bi.mm"
include "biimprcd.mm"
include "a1dd.mm"
include "syl9r.mm"
include "com34.mm"
include "jaod.mm"
include "sylan9r.mm"
include "sylan.mm"
include "ad2ant2lr.mm"
include "adantrl.mm"
include "rexlimdv.mm"
include "syld.mm"
include "impd.mm"
include "cbvralv.mm"
include "sylib.mm"
include "jca32.mm"
include "ex.mm"
include "orcom.mm"
include "elsn.mm"
include "df-or.mm"
include "bitr2i.mm"
include "3bitr4i.mm"
include "alrimiv.mm"
include "fvex.mm"
include "pwex.mm"
include "rabex.mm"
include "p0ex.mm"
include "unex.mm"
include "zorn.mm"
include "syl.mm"

theorem alexsubALTlem2
  let vx: setvar x
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vy: setvar y
  assume alexsubALT.1: |- X = U. J

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a z
  disjoint J a
  disjoint b c
  disjoint b d
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b z
  disjoint J b
  disjoint c d
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint J c
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d z
  disjoint J d
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint J u
  disjoint v x
  disjoint v z
  disjoint J v
  disjoint x z
  disjoint J x
  disjoint J z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a w
  disjoint a y
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b w
  disjoint b y
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c w
  disjoint c y
  disjoint d f
  disjoint d m
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d w
  disjoint d y
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
  disjoint u w
  disjoint u y
  disjoint v w
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x y
  disjoint y z
  disjoint J y
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X y
  assert |- ( ( ( J = ( topGen ` ( fi ` x ) ) /\ A. c e. ~P x ( X = U. c -> E. d e. ( ~P c i^i Fin ) X = U. d ) /\ a e. ~P ( fi ` x ) ) /\ A. b e. ( ~P a i^i Fin ) -. X = U. b ) -> E. u e. ( { z e. ~P ( fi ` x ) | ( a C_ z /\ A. b e. ( ~P z i^i Fin ) -. X = U. b ) } u. { (/) } ) A. v e. ( { z e. ~P ( fi ` x ) | ( a C_ z /\ A. b e. ( ~P z i^i Fin ) -. X = U. b ) } u. { (/) } ) -. u C. v )

  proof
    cJ
    vx
    cv
    #
    cfi
    cfv
    #
    ctg
    cfv
    wceq
    cX
    vc
    cv
    #
    cuni
    wceq
    cX
    vd
    cv
    cuni
    wceq
    vd
    @2
    cpw
    cfn
    cin
    wrex
    wi
    vc
    @0
    cpw
    wral
    va
    cv
    #
    @1
    cpw
    #
    wcel
    w3a
    #
    cX
    vb
    cv
    #
    cuni
    #
    wceq
    #
    wn
    #
    vb
    @3
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    vy
    cv
    #
    @3
    vz
    cv
    #
    wss
    #
    @9
    vb
    @15
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    vz
    @4
    crab
    #
    c0
    csn
    #
    cun
    #
    wss
    #
    @14
    crpss
    wor
    #
    wa
    #
    @14
    cuni
    #
    @23
    wcel
    #
    wi
    #
    vy
    wal
    vu
    cv
    vv
    cv
    wpss
    wn
    vv
    @23
    wral
    vu
    @23
    wrex
    @13
    @29
    vy
    @13
    @26
    @28
    @13
    @26
    wa
    #
    @27
    c0
    wceq
    #
    wn
    #
    @27
    @4
    wcel
    #
    @3
    @27
    wss
    #
    @9
    vb
    @27
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    wa
    #
    wi
    #
    @28
    @30
    @32
    @39
    @30
    @32
    wa
    #
    @33
    @34
    @37
    @41
    @27
    @1
    wss
    #
    @33
    @26
    @42
    @13
    @32
    @24
    @42
    @25
    @24
    vw
    cv
    #
    @1
    wss
    #
    vw
    @14
    wral
    @42
    @24
    @44
    vw
    @14
    @24
    @43
    @14
    wcel
    #
    @43
    @23
    wcel
    #
    @44
    @14
    @23
    @43
    ssel
    #
    @46
    @43
    @4
    wcel
    #
    @3
    @43
    wss
    #
    @9
    vb
    @43
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    wa
    #
    @43
    c0
    wceq
    #
    wo
    #
    @44
    @46
    @43
    @21
    wcel
    #
    @43
    @22
    wcel
    #
    wo
    @56
    @43
    @21
    @22
    elun
    @57
    @54
    @58
    @55
    @20
    @53
    vz
    @43
    @4
    vz
    vw
    weq
    #
    @16
    @49
    @19
    @52
    @15
    @43
    @3
    sseq2
    @59
    @9
    vb
    @18
    @51
    @59
    @17
    @50
    cfn
    @15
    @43
    pweq
    ineq1d
    raleqdv
    anbi12d
    elrab
    #
    vw
    c0
    velsn
    orbi12i
    bitri
    #
    @54
    @44
    @55
    @48
    @44
    @53
    @43
    @1
    elpwi
    adantr
    @55
    @44
    c0
    @1
    wss
    @1
    0ss
    @43
    c0
    @1
    sseq1
    mpbiri
    jaoi
    sylbi
    syl6
    ralrimiv
    vw
    @14
    @1
    unissb
    sylibr
    adantr
    ad2antlr
    @27
    @1
    vy
    vuniex
    #
    elpw
    sylibr
    @30
    @32
    @34
    @32
    @14
    @22
    wss
    #
    wn
    #
    @30
    @34
    @31
    @63
    @14
    uni0b
    notbii
    @24
    @64
    @34
    wi
    @13
    @25
    @24
    @64
    @14
    @21
    cin
    #
    c0
    wne
    #
    @34
    @24
    @63
    @65
    c0
    @65
    c0
    wceq
    @24
    @63
    @14
    @21
    @22
    disjssun
    biimpcd
    necon3bd
    @66
    @43
    @65
    wcel
    #
    vw
    wex
    @34
    vw
    @65
    n0
    @67
    @34
    vw
    @67
    @45
    @54
    wa
    #
    @34
    @67
    @45
    @57
    wa
    @68
    @43
    @14
    @21
    elin
    @57
    @54
    @45
    @60
    anbi2i
    bitri
    @68
    @49
    @45
    @34
    @45
    @48
    @49
    @52
    simprrl
    @45
    @54
    simpl
    @3
    @43
    @14
    ssuni
    syl2anc
    sylbi
    exlimiv
    sylbi
    syl6
    ad2antrl
    syl5bi
    imp
    @41
    cX
    vn
    cv
    #
    cuni
    #
    wceq
    #
    wn
    #
    vn
    @36
    wral
    @37
    @41
    @72
    vn
    @36
    @69
    @36
    wcel
    @69
    @27
    wss
    #
    @69
    cfn
    wcel
    #
    wa
    @41
    @72
    @69
    @27
    elfpw
    @41
    @73
    @74
    @72
    @41
    @74
    @73
    @72
    @30
    @32
    @74
    @73
    @72
    wi
    @30
    @32
    @74
    wa
    #
    wa
    #
    @73
    @69
    @43
    wss
    #
    vw
    @14
    wrex
    #
    @72
    @30
    @75
    @73
    @78
    @30
    @75
    @73
    wa
    #
    wa
    @14
    c0
    wne
    #
    @25
    @74
    @73
    @78
    @75
    @80
    @30
    @73
    @32
    @80
    @74
    @31
    @14
    c0
    @14
    c0
    wceq
    @27
    c0
    cuni
    #
    c0
    @14
    c0
    unieq
    uni0
    syl6eq
    necon3bi
    adantr
    ad2antrl
    @13
    @24
    @25
    @79
    simplrr
    @30
    @32
    @74
    @73
    simprlr
    @30
    @75
    @73
    simprr
    vw
    @14
    @69
    finsschain
    syl22anc
    expr
    @76
    @77
    @72
    vw
    @14
    @30
    @74
    @45
    @77
    @72
    wi
    #
    wi
    #
    @32
    @30
    @74
    @83
    @12
    @24
    @74
    @83
    wi
    #
    @5
    @25
    @12
    cX
    @81
    wceq
    #
    wn
    #
    @24
    @84
    @12
    c0
    @11
    wcel
    #
    @86
    @87
    c0
    @10
    wcel
    c0
    cfn
    wcel
    @3
    0elpw
    0fin
    c0
    @10
    cfn
    elin
    mpbir2an
    @9
    @86
    vb
    c0
    @11
    @6
    c0
    wceq
    #
    @8
    @85
    @88
    @7
    @81
    cX
    @6
    c0
    unieq
    eqeq2d
    notbid
    rspccv
    mpi
    @86
    @24
    wa
    @45
    @74
    @82
    @24
    @45
    @46
    @86
    @74
    @82
    wi
    #
    @47
    @46
    @56
    @86
    @89
    @61
    @86
    @54
    @89
    @55
    @54
    @89
    wi
    @86
    @52
    @89
    @48
    @49
    @52
    @77
    @74
    @72
    @77
    @69
    @50
    wcel
    #
    @52
    @74
    @72
    wi
    #
    @69
    @43
    vn
    vex
    elpw
    @52
    @90
    @74
    @72
    @90
    @74
    wa
    @69
    @51
    wcel
    @52
    @72
    @69
    @50
    cfn
    elin
    @9
    @72
    vb
    @69
    @51
    vb
    vn
    weq
    #
    @8
    @71
    @92
    @7
    @70
    cX
    @6
    @69
    unieq
    eqeq2d
    notbid
    rspccv
    syl5bir
    expd
    syl5bir
    com23
    ad2antll
    a1i
    @86
    @55
    @77
    @74
    @72
    @55
    @77
    @69
    c0
    wceq
    #
    @86
    @91
    @55
    @77
    @69
    c0
    wss
    @93
    @43
    c0
    @69
    sseq2
    @69
    ss0
    syl6bi
    @86
    @93
    @72
    @74
    @93
    @72
    @86
    @93
    @71
    @85
    @93
    @70
    @81
    cX
    @69
    c0
    unieq
    eqeq2d
    notbid
    biimprcd
    a1dd
    syl9r
    com34
    jaod
    syl5bi
    sylan9r
    com23
    sylan
    ad2ant2lr
    imp
    adantrl
    rexlimdv
    syld
    expr
    com23
    impd
    syl5bi
    ralrimiv
    @72
    @9
    vn
    vb
    @36
    vn
    vb
    weq
    #
    @71
    @8
    @94
    @70
    @7
    cX
    @69
    @6
    unieq
    eqeq2d
    notbid
    cbvralv
    sylib
    jca32
    ex
    @27
    @22
    wcel
    #
    @27
    @21
    wcel
    #
    wo
    #
    @96
    @95
    wo
    @40
    @28
    @95
    @96
    orcom
    @97
    @31
    @39
    wo
    @40
    @95
    @31
    @96
    @39
    @27
    c0
    @62
    elsn
    @20
    @38
    vz
    @27
    @4
    @15
    @27
    wceq
    #
    @16
    @34
    @19
    @37
    @15
    @27
    @3
    sseq2
    @98
    @9
    vb
    @18
    @36
    @98
    @17
    @35
    cfn
    @15
    @27
    pweq
    ineq1d
    raleqdv
    anbi12d
    elrab
    orbi12i
    @31
    @39
    df-or
    bitr2i
    @27
    @21
    @22
    elun
    3bitr4i
    sylib
    ex
    alrimiv
    vu
    vv
    vy
    @23
    @21
    @22
    @20
    vz
    @4
    @1
    @0
    cfi
    fvex
    pwex
    rabex
    p0ex
    unex
    zorn
    syl
end
