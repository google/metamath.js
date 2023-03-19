include "cr1.mm"
include "com.mm"
include "cima.mm"
include "cuni.mm"
include "wf1o.mm"
include "c0.mm"
include "crdg.mm"
include "wf1.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wss.mm"
include "wo.mm"
include "wral.mm"
include "wa.mm"
include "fveq2.mm"
include "fvex.mm"
include "fun11iun.mm"
include "wcel.mm"
include "ccrd.mm"
include "ackbij2lem2.mm"
include "f1of1.mm"
include "syl.mm"
include "word.mm"
include "ordom.mm"
include "cfn.mm"
include "r1fin.mm"
include "ficardom.mm"
include "ordelss.mm"
include "sylancr.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "nnord.mm"
include "ordtri2or2.mm"
include "syl2an.mm"
include "wi.mm"
include "ackbij2lem4.mm"
include "ex.mm"
include "ancoms.mm"
include "orim12d.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "mprg.mm"
include "wfun.mm"
include "wb.mm"
include "rdgfun.mm"
include "funiunfv.mm"
include "eqcomd.mm"
include "f1eq1.mm"
include "mp2b.mm"
include "cdm.mm"
include "wlim.mm"
include "r1funlim.mm"
include "simpli.mm"
include "f1eq2.mm"
include "bitr4i.mm"
include "mpbir.mm"
include "rnuni.mm"
include "wrex.mm"
include "wex.mm"
include "eliun.mm"
include "df-rex.mm"
include "wfn.mm"
include "funfn.mm"
include "mpbi.mm"
include "rdgdmlim.mm"
include "limomss.mm"
include "ax-mp.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "eqsstrd.mm"
include "rneq.mm"
include "sseq1d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "sselda.mm"
include "exlimiv.mm"
include "csuc.mm"
include "peano2.mm"
include "fnfvima.mm"
include "mp3an12.mm"
include "cvv.mm"
include "vex.mm"
include "cardnn.mm"
include "cdom.mm"
include "wbr.mm"
include "simpri.mm"
include "sseli.mm"
include "onssr1.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "con0.mm"
include "nnon.mm"
include "onenon.mm"
include "finnum.mm"
include "carddom2.mm"
include "mpbird.mm"
include "eqsstr3d.mm"
include "sucssel.mm"
include "4syl.mm"
include "eleqtrrd.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "impbii.mm"
include "3bitri.mm"
include "eqriv.mm"
include "eqtri.mm"
include "dff1o5.mm"
include "mpbir2an.mm"
include "f1oeq1.mm"

theorem ackbij2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )
  assume ackbij.g: |- G = ( x e. _V |-> ( y e. ~P dom x |-> ( F ` ( x " y ) ) ) )
  assume ackbij.h: |- H = U. ( rec ( G , (/) ) " _om )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- H : U. ( R1 " _om ) -1-1-onto-> _om

  proof
    cr1
    com
    cima
    cuni
    #
    com
    cH
    wf1o
    #
    @0
    com
    cG
    c0
    crdg
    #
    com
    cima
    #
    cuni
    #
    wf1o
    #
    @5
    @0
    com
    @4
    wf1
    #
    @4
    crn
    #
    com
    wceq
    @6
    va
    com
    va
    cv
    #
    cr1
    cfv
    #
    ciun
    #
    com
    va
    com
    @8
    @2
    cfv
    #
    ciun
    #
    wf1
    #
    @9
    com
    @11
    wf1
    #
    @11
    vb
    cv
    #
    @2
    cfv
    #
    wss
    #
    @16
    @11
    wss
    #
    wo
    #
    vb
    com
    wral
    #
    wa
    @13
    va
    com
    va
    vb
    com
    @11
    @16
    @9
    com
    @8
    @15
    @2
    fveq2
    @8
    @2
    fvex
    fun11iun
    @8
    com
    wcel
    #
    @14
    @20
    @21
    @9
    @9
    ccrd
    cfv
    #
    @11
    wf1
    #
    @22
    com
    wss
    #
    @14
    @21
    @9
    @22
    @11
    wf1o
    @23
    vx
    vy
    @8
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem2
    @9
    @22
    @11
    f1of1
    syl
    @21
    com
    word
    #
    @22
    com
    wcel
    #
    @24
    ordom
    @21
    @9
    cfn
    wcel
    @26
    @8
    r1fin
    @9
    ficardom
    syl
    com
    @22
    ordelss
    sylancr
    @9
    @22
    com
    @11
    f1ss
    syl2anc
    @21
    @19
    vb
    com
    @21
    @15
    com
    wcel
    #
    wa
    #
    @8
    @15
    wss
    #
    @15
    @8
    wss
    #
    wo
    #
    @19
    @21
    @8
    word
    @15
    word
    @31
    @27
    @8
    nnord
    @15
    nnord
    @8
    @15
    ordtri2or2
    syl2an
    @28
    @29
    @17
    @30
    @18
    @27
    @21
    @29
    @17
    wi
    @27
    @21
    wa
    @29
    @17
    vx
    vy
    @15
    @8
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem4
    ex
    ancoms
    @28
    @30
    @18
    vx
    vy
    @8
    @15
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem4
    ex
    orim12d
    mpd
    ralrimiva
    jca
    mprg
    @6
    @0
    com
    @12
    wf1
    #
    @13
    @2
    wfun
    #
    @4
    @12
    wceq
    @6
    @32
    wb
    c0
    cG
    rdgfun
    #
    @33
    @12
    @4
    va
    com
    @2
    funiunfv
    eqcomd
    @0
    com
    @4
    @12
    f1eq1
    mp2b
    cr1
    wfun
    #
    @10
    @0
    wceq
    @13
    @32
    wb
    @35
    cr1
    cdm
    #
    wlim
    #
    r1funlim
    simpli
    va
    com
    cr1
    funiunfv
    @10
    @0
    com
    @12
    f1eq2
    mp2b
    bitr4i
    mpbir
    @7
    va
    @3
    @8
    crn
    #
    ciun
    #
    com
    va
    @3
    rnuni
    vb
    @39
    com
    @15
    @39
    wcel
    @15
    @38
    wcel
    #
    va
    @3
    wrex
    @8
    @3
    wcel
    #
    @40
    wa
    #
    va
    wex
    #
    @27
    va
    @15
    @3
    @38
    eliun
    @40
    va
    @3
    df-rex
    @43
    @27
    @42
    @27
    va
    @41
    @38
    com
    @15
    @41
    vc
    cv
    #
    @2
    cfv
    #
    @8
    wceq
    #
    vc
    com
    wrex
    #
    @38
    com
    wss
    #
    @2
    @2
    cdm
    #
    wfn
    #
    com
    @49
    wss
    #
    @41
    @47
    wb
    @33
    @50
    @34
    @2
    funfn
    mpbi
    #
    @49
    wlim
    @51
    c0
    cG
    rdgdmlim
    @49
    limomss
    ax-mp
    #
    vc
    @49
    com
    @8
    @2
    fvelimab
    mp2an
    @46
    @48
    vc
    com
    @44
    com
    wcel
    #
    @45
    crn
    #
    com
    wss
    @46
    @48
    @54
    @55
    @44
    cr1
    cfv
    #
    ccrd
    cfv
    #
    com
    @54
    @56
    @57
    @45
    wf1o
    @56
    @57
    @45
    wfo
    @55
    @57
    wceq
    vx
    vy
    @44
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem2
    @56
    @57
    @45
    f1ofo
    @56
    @57
    @45
    forn
    3syl
    @54
    @25
    @57
    com
    wcel
    #
    @57
    com
    wss
    ordom
    @54
    @56
    cfn
    wcel
    @58
    @44
    r1fin
    @56
    ficardom
    syl
    com
    @57
    ordelss
    sylancr
    eqsstrd
    @46
    @55
    @38
    com
    @45
    @8
    rneq
    sseq1d
    syl5ibcom
    rexlimiv
    sylbi
    sselda
    exlimiv
    @27
    @15
    csuc
    #
    @2
    cfv
    #
    @3
    wcel
    #
    @15
    @60
    crn
    #
    wcel
    #
    @43
    @27
    @59
    com
    wcel
    #
    @61
    @15
    peano2
    #
    @50
    @51
    @64
    @61
    @52
    @53
    @49
    com
    @2
    @59
    fnfvima
    mp3an12
    syl
    @27
    @15
    @59
    cr1
    cfv
    #
    ccrd
    cfv
    #
    @62
    @15
    cvv
    wcel
    @27
    @59
    @67
    wss
    #
    @15
    @67
    wcel
    vb
    vex
    @27
    @64
    @68
    @65
    @64
    @59
    @59
    ccrd
    cfv
    #
    @67
    @59
    cardnn
    @64
    @69
    @67
    wss
    #
    @59
    @66
    cdom
    wbr
    #
    @66
    cvv
    wcel
    @64
    @59
    @66
    wss
    #
    @71
    @59
    cr1
    fvex
    @64
    @59
    @36
    wcel
    @72
    com
    @36
    @59
    @37
    com
    @36
    wss
    @35
    @37
    r1funlim
    simpri
    @36
    limomss
    ax-mp
    sseli
    @59
    onssr1
    syl
    @59
    @66
    cvv
    ssdomg
    mpsyl
    @64
    @59
    ccrd
    cdm
    #
    wcel
    #
    @66
    @73
    wcel
    #
    @70
    @71
    wb
    @64
    @59
    con0
    wcel
    @74
    @59
    nnon
    @59
    onenon
    syl
    @64
    @66
    cfn
    wcel
    @75
    @59
    r1fin
    @66
    finnum
    syl
    @59
    @66
    carddom2
    syl2anc
    mpbird
    eqsstr3d
    syl
    @15
    @67
    cvv
    sucssel
    mpsyl
    @27
    @64
    @66
    @67
    @60
    wf1o
    @66
    @67
    @60
    wfo
    @62
    @67
    wceq
    @65
    vx
    vy
    @59
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem2
    @66
    @67
    @60
    f1ofo
    @66
    @67
    @60
    forn
    4syl
    eleqtrrd
    @42
    @61
    @63
    wa
    va
    @60
    @59
    @2
    fvex
    @8
    @60
    wceq
    #
    @41
    @61
    @40
    @63
    @8
    @60
    @3
    eleq1
    @76
    @38
    @62
    @15
    @8
    @60
    rneq
    eleq2d
    anbi12d
    spcev
    syl2anc
    impbii
    3bitri
    eqriv
    eqtri
    @0
    com
    @4
    dff1o5
    mpbir2an
    cH
    @4
    wceq
    @1
    @5
    wb
    ackbij.h
    @0
    com
    cH
    @4
    f1oeq1
    ax-mp
    mpbir
end
