include "cdm.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wfun.mm"
include "wcel.mm"
include "crn.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "wceq.mm"
include "wi.mm"
include "cid.mm"
include "cres.mm"
include "w3a.mm"
include "cdif.mm"
include "wwe.mm"
include "wa.mm"
include "coi.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "dmeqi.mm"
include "dmopab.mm"
include "eqtri.mm"
include "simp3.mm"
include "simp1.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "selpw.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "exlimiv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "funopab4.mm"
include "funeqi.mm"
include "mpbir.mm"
include "breq1.mm"
include "elrab.mm"
include "wf1.mm"
include "brdomi.mm"
include "cun.mm"
include "cin.mm"
include "wf.mm"
include "f1f.mm"
include "adantl.mm"
include "frn.mm"
include "syl.mm"
include "resss.mm"
include "ssun2.mm"
include "sstri.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "fssxp.mm"
include "mp2b.mm"
include "ssini.mm"
include "a1i.mm"
include "inss2.mm"
include "3jca.mm"
include "cep.mm"
include "word.mm"
include "eloni.mm"
include "ordwe.mm"
include "adantr.mm"
include "wiso.mm"
include "wb.mm"
include "cfv.mm"
include "wrex.mm"
include "f1f1orn.mm"
include "f1oiso.mm"
include "sylancl.mm"
include "isores2.mm"
include "sylib.mm"
include "isowe.mm"
include "mpbid.mm"
include "c0.mm"
include "wn.mm"
include "wal.mm"
include "wor.mm"
include "weso.mm"
include "brel.mm"
include "simpld.mm"
include "sonr.mm"
include "syl2an.mm"
include "pm2.01da.mm"
include "alrimiv.mm"
include "intirr.mm"
include "disj3.mm"
include "weeq1.mm"
include "isoeq3.mm"
include "wse.mm"
include "cvv.mm"
include "vex.mm"
include "rnex.mm"
include "exse.mm"
include "ax-mp.mm"
include "eqid.mm"
include "oieu.mm"
include "mpbi2and.mm"
include "xpex.mm"
include "inex2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "dmss.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "dmresi.mm"
include "sseq2.mm"
include "syl5eqssr.mm"
include "eqssd.mm"
include "sseq1d.mm"
include "reseq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "sqxpeqd.mm"
include "3anbi123d.mm"
include "difeq1.mm"
include "difun2.mm"
include "ineq1i.mm"
include "indif1.mm"
include "3eqtr3i.mm"
include "syl6eq.mm"
include "weeq2.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "oieq1.mm"
include "oieq2.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "eqeq2d.mm"
include "spcev.mm"
include "syl21anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylan2.mm"
include "simpr.mm"
include "dmex.mm"
include "oion.mm"
include "syl6eqel.mm"
include "cen.mm"
include "simplr.mm"
include "oien.mm"
include "sylancr.mm"
include "eqbrtrd.mm"
include "simpll1.mm"
include "ssdomg.mm"
include "endomtr.mm"
include "jca.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "abbi2dv.mm"
include "rneqi.mm"
include "rnopab.mm"
include "syl6reqr.mm"
include "3pm3.2i.mm"

theorem hartogslem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  assume hartogslem.2: |- F = { <. r , y >. | ( ( ( dom r C_ A /\ ( _I |` dom r ) C_ r /\ r C_ ( dom r X. dom r ) ) /\ ( r \ _I ) We dom r ) /\ y = dom OrdIso ( ( r \ _I ) , dom r ) ) }
  assume hartogslem.3: |- R = { <. s , t >. | E. w e. y E. z e. y ( ( s = ( f ` w ) /\ t = ( f ` z ) ) /\ w _E z ) }

  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint f r
  disjoint f x
  disjoint A f
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R r
  disjoint R x
  disjoint V r
  disjoint V y
  assert |- ( dom F C_ ~P ( A X. A ) /\ Fun F /\ ( A e. V -> ran F = { x e. On | x ~<_ A } ) )

  proof
    cF
    cdm
    #
    cA
    cA
    cxp
    #
    cpw
    #
    wss
    cF
    wfun
    #
    cA
    cV
    wcel
    #
    cF
    crn
    #
    vx
    cv
    #
    cA
    cdom
    wbr
    #
    vx
    con0
    crab
    #
    wceq
    wi
    @0
    vr
    cv
    #
    cdm
    #
    cA
    wss
    #
    cid
    @10
    cres
    #
    @9
    wss
    #
    @9
    @10
    @10
    cxp
    #
    wss
    #
    w3a
    #
    @10
    @9
    cid
    cdif
    #
    wwe
    #
    wa
    #
    vy
    cv
    #
    @10
    @17
    coi
    #
    cdm
    #
    wceq
    #
    wa
    #
    vy
    wex
    #
    vr
    cab
    #
    @2
    @0
    @24
    vr
    vy
    copab
    #
    cdm
    @26
    cF
    @27
    hartogslem.2
    dmeqi
    @24
    vr
    vy
    dmopab
    eqtri
    @25
    vr
    @2
    @24
    @9
    @2
    wcel
    #
    vy
    @16
    @28
    @18
    @23
    @16
    @9
    @1
    wss
    @28
    @16
    @9
    @14
    @1
    @11
    @13
    @15
    simp3
    @16
    @11
    @11
    @14
    @1
    wss
    @11
    @13
    @15
    simp1
    #
    @29
    @10
    cA
    @10
    cA
    xpss12
    syl2anc
    sstrd
    vr
    @1
    selpw
    sylibr
    ad2antrr
    exlimiv
    abssi
    eqsstri
    @3
    @27
    wfun
    @19
    vr
    vy
    @22
    funopab4
    cF
    @27
    hartogslem.2
    funeqi
    mpbir
    @4
    @8
    @24
    vr
    wex
    #
    vy
    cab
    #
    @5
    @4
    @30
    vy
    @8
    @20
    @8
    wcel
    @20
    con0
    wcel
    #
    @20
    cA
    cdom
    wbr
    #
    wa
    #
    @4
    @30
    @7
    @33
    vx
    @20
    con0
    @6
    @20
    cA
    cdom
    breq1
    elrab
    @4
    @34
    @30
    @33
    @32
    @20
    cA
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @30
    @20
    cA
    vf
    brdomi
    @32
    @37
    @30
    @32
    @36
    @30
    vf
    @32
    @36
    @30
    @32
    @36
    wa
    #
    @35
    crn
    #
    cA
    wss
    #
    cid
    @39
    cres
    #
    cR
    cid
    cun
    #
    @39
    @39
    cxp
    #
    cin
    #
    wss
    #
    @44
    @43
    wss
    #
    w3a
    #
    @39
    cR
    @43
    cin
    #
    cid
    cdif
    #
    wwe
    #
    @20
    @39
    @49
    coi
    #
    cdm
    #
    wceq
    #
    @30
    @38
    @40
    @45
    @46
    @38
    @20
    cA
    @35
    wf
    #
    @40
    @36
    @54
    @32
    @20
    cA
    @35
    f1f
    adantl
    @20
    cA
    @35
    frn
    syl
    @45
    @38
    @41
    @42
    @43
    @41
    cid
    @42
    cid
    @39
    resss
    cid
    cR
    ssun2
    sstri
    @39
    @39
    @41
    wf1o
    @39
    @39
    @41
    wf
    @41
    @43
    wss
    @39
    f1oi
    @39
    @39
    @41
    f1of
    @39
    @39
    @41
    fssxp
    mp2b
    ssini
    #
    a1i
    @46
    @38
    @42
    @43
    inss2
    #
    a1i
    3jca
    @38
    @39
    @48
    wwe
    #
    @50
    @38
    @20
    cep
    wwe
    #
    @57
    @32
    @58
    @36
    @32
    @20
    word
    #
    @58
    @20
    eloni
    #
    @20
    ordwe
    syl
    adantr
    @38
    @20
    @39
    cep
    @48
    @35
    wiso
    #
    @58
    @57
    wb
    @38
    @20
    @39
    cep
    cR
    @35
    wiso
    #
    @61
    @38
    @20
    @39
    @35
    wf1o
    #
    cR
    vs
    cv
    vw
    cv
    #
    @35
    cfv
    wceq
    vt
    cv
    vz
    cv
    #
    @35
    cfv
    wceq
    wa
    @64
    @65
    cep
    wbr
    wa
    vz
    @20
    wrex
    vw
    @20
    wrex
    vs
    vt
    copab
    wceq
    @62
    @36
    @63
    @32
    @20
    cA
    @35
    f1f1orn
    adantl
    hartogslem.3
    vw
    vz
    vs
    vt
    @20
    @39
    cep
    cR
    @35
    f1oiso
    sylancl
    @20
    @39
    cep
    cR
    @35
    isores2
    sylib
    #
    @20
    @39
    cep
    @48
    @35
    isowe
    syl
    mpbid
    #
    @38
    @48
    @49
    wceq
    #
    @57
    @50
    wb
    @38
    @48
    cid
    cin
    c0
    wceq
    #
    @68
    @38
    @6
    @6
    @48
    wbr
    #
    wn
    #
    vx
    wal
    @69
    @38
    @71
    vx
    @38
    @70
    @38
    @39
    @48
    wor
    #
    @6
    @39
    wcel
    #
    @71
    @70
    @38
    @57
    @72
    @67
    @39
    @48
    weso
    syl
    @70
    @73
    @73
    @6
    @6
    @39
    @39
    @48
    cR
    @43
    inss2
    brel
    simpld
    @39
    @6
    @48
    sonr
    syl2an
    pm2.01da
    alrimiv
    vx
    @48
    intirr
    sylibr
    @48
    cid
    disj3
    sylib
    #
    @39
    @48
    @49
    weeq1
    syl
    mpbid
    #
    @38
    @53
    @35
    @51
    wceq
    #
    @38
    @59
    @20
    @39
    cep
    @49
    @35
    wiso
    #
    @53
    @76
    wa
    #
    @32
    @59
    @36
    @60
    adantr
    @38
    @61
    @77
    @66
    @38
    @68
    @61
    @77
    wb
    @74
    @20
    @39
    cep
    @48
    @49
    @35
    isoeq3
    syl
    mpbid
    @38
    @50
    @39
    @49
    wse
    #
    @59
    @77
    wa
    @78
    wb
    @75
    @39
    cvv
    wcel
    @79
    @35
    vf
    vex
    rnex
    #
    @39
    @49
    cvv
    exse
    ax-mp
    @39
    @20
    @49
    @51
    @35
    @51
    eqid
    oieu
    sylancl
    mpbi2and
    simpld
    @24
    @47
    @50
    wa
    #
    @53
    wa
    vr
    @44
    @43
    @42
    @39
    @39
    @80
    @80
    xpex
    inex2
    @9
    @44
    wceq
    #
    @19
    @81
    @23
    @53
    @82
    @16
    @47
    @18
    @50
    @82
    @11
    @40
    @13
    @45
    @15
    @46
    @82
    @10
    @39
    cA
    @82
    @10
    @39
    @82
    @10
    @43
    cdm
    #
    @39
    @82
    @9
    @43
    wss
    #
    @10
    @83
    wss
    @82
    @84
    @46
    @56
    @9
    @44
    @43
    sseq1
    mpbiri
    @9
    @43
    dmss
    syl
    @39
    dmxpid
    syl6sseq
    @82
    @39
    @41
    cdm
    #
    @10
    @39
    dmresi
    @82
    @41
    @9
    wss
    #
    @85
    @10
    wss
    @82
    @86
    @45
    @55
    @9
    @44
    @41
    sseq2
    mpbiri
    @41
    @9
    dmss
    syl
    syl5eqssr
    eqssd
    #
    sseq1d
    @82
    @12
    @41
    @9
    @44
    @82
    @10
    @39
    cid
    @87
    reseq2d
    @82
    id
    #
    sseq12d
    @82
    @9
    @44
    @14
    @43
    @88
    @82
    @10
    @39
    @87
    sqxpeqd
    sseq12d
    3anbi123d
    @82
    @18
    @10
    @49
    wwe
    #
    @50
    @82
    @17
    @49
    wceq
    #
    @18
    @89
    wb
    @82
    @17
    @44
    cid
    cdif
    #
    @49
    @9
    @44
    cid
    difeq1
    @42
    cid
    cdif
    #
    @43
    cin
    cR
    cid
    cdif
    #
    @43
    cin
    @91
    @49
    @92
    @93
    @43
    cR
    cid
    difun2
    ineq1i
    @42
    @43
    cid
    indif1
    cR
    @43
    cid
    indif1
    3eqtr3i
    syl6eq
    #
    @10
    @17
    @49
    weeq1
    syl
    @82
    @10
    @39
    wceq
    #
    @89
    @50
    wb
    @87
    @10
    @39
    @49
    weeq2
    syl
    bitrd
    anbi12d
    @82
    @22
    @52
    @20
    @82
    @21
    @51
    @82
    @21
    @10
    @49
    coi
    #
    @51
    @82
    @90
    @21
    @96
    wceq
    @94
    @10
    @17
    @49
    oieq1
    syl
    @82
    @95
    @96
    @51
    wceq
    @87
    @10
    @39
    @49
    oieq2
    syl
    eqtrd
    dmeqd
    eqeq2d
    anbi12d
    spcev
    syl21anc
    ex
    exlimdv
    imp
    sylan2
    @4
    @24
    @34
    vr
    @4
    @24
    @34
    @4
    @24
    wa
    #
    @32
    @33
    @24
    @32
    @4
    @24
    @20
    @22
    con0
    @19
    @23
    simpr
    #
    @10
    cvv
    wcel
    #
    @22
    con0
    wcel
    @9
    vr
    vex
    dmex
    #
    @10
    @17
    @21
    cvv
    @21
    eqid
    #
    oion
    ax-mp
    syl6eqel
    adantl
    @97
    @20
    @10
    cen
    wbr
    #
    @10
    cA
    cdom
    wbr
    #
    @33
    @24
    @102
    @4
    @24
    @20
    @22
    @10
    cen
    @98
    @24
    @99
    @18
    @22
    @10
    cen
    wbr
    @100
    @16
    @18
    @23
    simplr
    @10
    @17
    @21
    cvv
    @101
    oien
    sylancr
    eqbrtrd
    adantl
    @24
    @4
    @11
    @103
    @11
    @13
    @15
    @18
    @23
    simpll1
    @4
    @11
    @103
    @10
    cA
    cV
    ssdomg
    imp
    sylan2
    @20
    @10
    cA
    endomtr
    syl2anc
    jca
    ex
    exlimdv
    impbid2
    syl5bb
    abbi2dv
    @5
    @27
    crn
    @31
    cF
    @27
    hartogslem.2
    rneqi
    @24
    vr
    vy
    rnopab
    eqtri
    syl6reqr
    3pm3.2i
end
