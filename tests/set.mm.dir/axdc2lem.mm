include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "wbr.mm"
include "com.mm"
include "wral.mm"
include "wex.mm"
include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "wss.mm"
include "crab.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "eldifsni.mm"
include "n0.mm"
include "sylib.mm"
include "syl.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "copab.mm"
include "dmeqi.mm"
include "cab.mm"
include "19.42v.mm"
include "abbii.mm"
include "dmopab.mm"
include "df-rab.mm"
include "3eqtr4i.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "neeq1d.mm"
include "biimparc.mm"
include "wi.mm"
include "wal.mm"
include "eldifi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "3syl.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "alrimiv.mm"
include "rneqi.mm"
include "rnopab.mm"
include "sseq1i.mm"
include "abss.mm"
include "bitri.mm"
include "sseqtr4d.mm"
include "adantl.mm"
include "cvv.mm"
include "cun.mm"
include "cuni.mm"
include "cxp.mm"
include "fvrn0.mm"
include "elssuni.mm"
include "ax-mp.mm"
include "sseli.mm"
include "anim2i.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "3sstr4i.mm"
include "frn.mm"
include "pwex.mm"
include "difexg.mm"
include "ssex.mm"
include "p0ex.mm"
include "unexg.mm"
include "sylancl.mm"
include "uniexg.mm"
include "xpexg.mm"
include "sylancr.mm"
include "ssexg.mm"
include "vex.mm"
include "eldm.mm"
include "exbii.mm"
include "bitr2i.mm"
include "dmeq.mm"
include "syl5bb.mm"
include "rneq.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "breq.mm"
include "ralbidv.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "ax-dc.mm"
include "vtoclg.mm"
include "mp2and.mm"
include "simpr.mm"
include "fveq2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccv.mm"
include "fvex.mm"
include "breldm.mm"
include "syl6.mm"
include "imp.mm"
include "adantll.mm"
include "wb.mm"
include "eleq2.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "fmptd.mm"
include "ex.mm"
include "impcom.mm"
include "fvmpt.mm"
include "peano2.mm"
include "fvmptg.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "brab.mm"
include "simprbi.mm"
include "syl6bir.mm"
include "ralimia.mm"
include "adantr.mm"
include "cmpt.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbi.mm"
include "dcomex.mm"
include "rnex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"
include "eqeltri.mm"
include "feq1.mm"
include "fveq1.mm"
include "eleq12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "exlimiv.mm"
include "sylc.mm"

theorem axdc2lem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vr: setvar r
  assume axdc2lem.1: |- A e. _V
  assume axdc2lem.2: |- R = { <. x , y >. | ( x e. A /\ y e. ( F ` x ) ) }
  assume axdc2lem.3: |- G = ( x e. _om |-> ( h ` x ) )

  disjoint A g
  disjoint A h
  disjoint g h
  disjoint A x
  disjoint A y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint F g
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G k
  disjoint g k
  disjoint G x
  disjoint G y
  disjoint k x
  disjoint k y
  disjoint R h
  disjoint R k
  disjoint R x
  disjoint h k
  disjoint R r
  disjoint h r
  disjoint k r
  disjoint r x
  disjoint r y
  assert |- ( ( A =/= (/) /\ F : A --> ( ~P A \ { (/) } ) ) -> E. g ( g : _om --> A /\ A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) )

  proof
    cA
    c0
    wne
    #
    cA
    cA
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cF
    wf
    #
    wa
    #
    vk
    cv
    #
    vh
    cv
    #
    cfv
    #
    @6
    csuc
    #
    @7
    cfv
    #
    cR
    wbr
    #
    vk
    com
    wral
    #
    vh
    wex
    #
    @4
    com
    cA
    vg
    cv
    #
    wf
    #
    @9
    @14
    cfv
    #
    @6
    @14
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vk
    com
    wral
    #
    wa
    #
    vg
    wex
    #
    @5
    cR
    cdm
    #
    c0
    wne
    #
    cR
    crn
    #
    @23
    wss
    #
    @13
    @4
    @24
    @0
    @4
    @23
    cA
    c0
    @4
    cA
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vy
    wex
    #
    vx
    cA
    crab
    #
    @23
    @4
    @31
    vx
    cA
    wral
    cA
    @32
    wceq
    @4
    @31
    vx
    cA
    @4
    @28
    cA
    wcel
    #
    wa
    #
    @29
    @3
    wcel
    #
    @31
    cA
    @3
    @28
    cF
    ffvelrn
    #
    @35
    @29
    c0
    wne
    @31
    @29
    @1
    c0
    eldifsni
    vy
    @29
    n0
    sylib
    syl
    ralrimiva
    @31
    vx
    cA
    rabid2
    sylibr
    @23
    @33
    @30
    wa
    #
    vx
    vy
    copab
    #
    cdm
    #
    @32
    cR
    @38
    axdc2lem.2
    dmeqi
    @37
    vy
    wex
    #
    vx
    cab
    @33
    @31
    wa
    #
    vx
    cab
    @39
    @32
    @40
    @41
    vx
    @33
    @30
    vy
    19.42v
    abbii
    @37
    vx
    vy
    dmopab
    @31
    vx
    cA
    df-rab
    3eqtr4i
    eqtri
    syl6reqr
    #
    neeq1d
    biimparc
    @4
    @26
    @0
    @4
    @25
    cA
    @23
    @4
    @37
    vx
    wex
    #
    @27
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    @25
    cA
    wss
    #
    @4
    @45
    vy
    @4
    @37
    @44
    vx
    @4
    @33
    @30
    @44
    @34
    @35
    @29
    @1
    wcel
    #
    @30
    @44
    wi
    @36
    @29
    @1
    @2
    eldifi
    @30
    @48
    @44
    @27
    @29
    cA
    elelpwi
    expcom
    3syl
    expimpd
    exlimdv
    alrimiv
    @47
    @43
    vy
    cab
    #
    cA
    wss
    @46
    @25
    @49
    cA
    @25
    @38
    crn
    @49
    cR
    @38
    axdc2lem.2
    rneqi
    @37
    vx
    vy
    rnopab
    eqtri
    sseq1i
    @43
    vy
    cA
    abss
    bitri
    sylibr
    @42
    sseqtr4d
    adantl
    @5
    cR
    cvv
    wcel
    #
    @24
    @26
    wa
    #
    @13
    wi
    #
    @5
    cR
    cA
    cF
    crn
    #
    @2
    cun
    #
    cuni
    #
    cxp
    #
    wss
    @56
    cvv
    wcel
    #
    @50
    @38
    @33
    @27
    @55
    wcel
    #
    wa
    #
    vx
    vy
    copab
    cR
    @56
    @37
    @59
    vx
    vy
    @30
    @58
    @33
    @29
    @55
    @27
    @29
    @54
    wcel
    @29
    @55
    wss
    cF
    @28
    fvrn0
    @29
    @54
    elssuni
    ax-mp
    sseli
    anim2i
    ssopab2i
    axdc2lem.2
    vx
    vy
    cA
    @55
    df-xp
    3sstr4i
    @5
    cA
    cvv
    wcel
    @55
    cvv
    wcel
    #
    @57
    axdc2lem.1
    @5
    @54
    cvv
    wcel
    #
    @60
    @5
    @53
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @61
    @5
    @53
    @3
    wss
    #
    @62
    @4
    @63
    @0
    cA
    @3
    cF
    frn
    adantl
    @53
    @3
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    cA
    axdc2lem.1
    pwex
    @1
    @2
    cvv
    difexg
    ax-mp
    ssex
    syl
    p0ex
    @53
    @2
    cvv
    cvv
    unexg
    sylancl
    @54
    cvv
    uniexg
    syl
    cA
    @55
    cvv
    cvv
    xpexg
    sylancr
    cR
    @56
    cvv
    ssexg
    sylancr
    @28
    @27
    vr
    cv
    #
    wbr
    vy
    wex
    #
    vx
    wex
    #
    @64
    crn
    #
    @64
    cdm
    #
    wss
    #
    wa
    #
    @8
    @10
    @64
    wbr
    #
    vk
    com
    wral
    #
    vh
    wex
    #
    wi
    @52
    vr
    cR
    cvv
    @64
    cR
    wceq
    #
    @70
    @51
    @73
    @13
    @74
    @66
    @24
    @69
    @26
    @66
    @68
    c0
    wne
    #
    @74
    @24
    @75
    @28
    @68
    wcel
    #
    vx
    wex
    @66
    vx
    @68
    n0
    @76
    @65
    vx
    vy
    @28
    @64
    vx
    vex
    eldm
    exbii
    bitr2i
    @74
    @68
    @23
    c0
    @64
    cR
    dmeq
    #
    neeq1d
    syl5bb
    @74
    @67
    @25
    @68
    @23
    @64
    cR
    rneq
    @77
    sseq12d
    anbi12d
    @74
    @72
    @12
    vh
    @74
    @71
    @11
    vk
    com
    @8
    @10
    @64
    cR
    breq
    ralbidv
    exbidv
    imbi12d
    vr
    vx
    vy
    vh
    vk
    ax-dc
    vtoclg
    syl
    mp2and
    @0
    @4
    simpr
    @12
    @4
    @22
    wi
    vh
    @12
    @4
    @22
    @12
    @4
    wa
    com
    cA
    cG
    wf
    #
    @9
    cG
    cfv
    #
    @6
    cG
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vk
    com
    wral
    #
    @22
    @4
    @12
    @78
    @4
    @23
    cA
    wceq
    #
    @12
    @78
    wi
    @42
    @84
    @12
    @78
    @84
    @12
    wa
    #
    vx
    com
    @28
    @7
    cfv
    #
    cA
    cG
    @85
    @28
    com
    wcel
    #
    wa
    @86
    @23
    wcel
    #
    @86
    cA
    wcel
    #
    @12
    @87
    @88
    @84
    @12
    @87
    @88
    @12
    @87
    @86
    @28
    csuc
    #
    @7
    cfv
    #
    cR
    wbr
    #
    @88
    @11
    @92
    vk
    @28
    com
    @6
    @28
    wceq
    #
    @8
    @86
    @10
    @91
    cR
    @6
    @28
    @7
    fveq2
    @93
    @9
    @90
    @7
    @6
    @28
    suceq
    fveq2d
    breq12d
    rspccv
    @86
    @91
    cR
    @28
    @7
    fvex
    @90
    @7
    fvex
    breldm
    syl6
    imp
    adantll
    @84
    @88
    @89
    wb
    @12
    @87
    @23
    cA
    @86
    eleq2
    ad2antrr
    mpbid
    axdc2lem.3
    fmptd
    ex
    syl
    impcom
    @12
    @83
    @4
    @11
    @82
    vk
    com
    @6
    com
    wcel
    #
    @11
    @80
    @79
    cR
    wbr
    #
    @82
    @94
    @80
    @8
    @79
    @10
    cR
    vx
    @6
    @86
    @8
    com
    cG
    @28
    @6
    @7
    fveq2
    axdc2lem.3
    @6
    @7
    fvex
    fvmpt
    @94
    @9
    com
    wcel
    @10
    cvv
    wcel
    @79
    @10
    wceq
    @6
    peano2
    @9
    @7
    fvex
    vx
    @9
    @86
    @10
    com
    cvv
    cG
    @28
    @9
    @7
    fveq2
    axdc2lem.3
    fvmptg
    sylancl
    breq12d
    @95
    @80
    cA
    wcel
    #
    @82
    @37
    @96
    @27
    @81
    wcel
    #
    wa
    @96
    @82
    wa
    vx
    vy
    @80
    @79
    cR
    @6
    cG
    fvex
    @9
    cG
    fvex
    @28
    @80
    wceq
    #
    @33
    @96
    @30
    @97
    @28
    @80
    cA
    eleq1
    @98
    @29
    @81
    @27
    @28
    @80
    cF
    fveq2
    eleq2d
    anbi12d
    @27
    @79
    wceq
    @97
    @82
    @96
    @27
    @79
    @81
    eleq1
    anbi2d
    axdc2lem.2
    brab
    simprbi
    syl6bir
    ralimia
    adantr
    @21
    @78
    @83
    wa
    vg
    cG
    cG
    vx
    com
    @86
    cmpt
    #
    cvv
    axdc2lem.3
    com
    @7
    crn
    #
    @2
    cun
    #
    @99
    wf
    #
    com
    cvv
    wcel
    @101
    cvv
    wcel
    @99
    cvv
    wcel
    @86
    @101
    wcel
    #
    vx
    com
    wral
    @102
    @103
    vx
    com
    @7
    @28
    fvrn0
    rgenw
    vx
    com
    @101
    @86
    @99
    @99
    eqid
    fmpt
    mpbi
    dcomex
    @100
    @2
    @7
    vh
    vex
    rnex
    p0ex
    unex
    com
    @101
    @99
    cvv
    cvv
    fex2
    mp3an
    eqeltri
    @14
    cG
    wceq
    #
    @15
    @78
    @20
    @83
    com
    cA
    @14
    cG
    feq1
    @104
    @19
    @82
    vk
    com
    @104
    @16
    @79
    @18
    @81
    @9
    @14
    cG
    fveq1
    @104
    @17
    @80
    cF
    @6
    @14
    cG
    fveq1
    fveq2d
    eleq12d
    ralbidv
    anbi12d
    spcev
    syl2anc
    ex
    exlimiv
    sylc
end
