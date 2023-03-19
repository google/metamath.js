include "com.mm"
include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "wf1.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "wb.mm"
include "fveq2.mm"
include "f1eq1.mm"
include "syl.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "crdg.mm"
include "cres.mm"
include "fveq1i.mm"
include "vex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "rneqi.mm"
include "unieqi.mm"
include "sseq1i.mm"
include "anbi12i.mm"
include "sylanbrc.mm"
include "w3a.mm"
include "wpss.mm"
include "wal.mm"
include "fvex.mm"
include "rneq.mm"
include "psseq12d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "imp.mm"
include "pssss.mm"
include "sstr.mm"
include "sylan.mm"
include "expcom.mm"
include "anim2d.mm"
include "ad2antll.mm"
include "mpd.mm"
include "3adant1.mm"
include "frsuc.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "3exp.mm"
include "a2d.mm"
include "finds.mm"
include "impcom.mm"

theorem fin23lem34
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let cB: class B
  assume fin23lem33.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }
  assume fin23lem.f: |- ( ph -> h : _om -1-1-> _V )
  assume fin23lem.g: |- ( ph -> U. ran h C_ G )
  assume fin23lem.h: |- ( ph -> A. j ( ( j : _om -1-1-> _V /\ U. ran j C_ G ) -> ( ( i ` j ) : _om -1-1-> _V /\ U. ran ( i ` j ) C. U. ran j ) ) )
  assume fin23lem.i: |- Y = ( rec ( i , h ) |` _om )

  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint g i
  disjoint g j
  disjoint g x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint A a
  disjoint A j
  disjoint a h
  disjoint G a
  disjoint g h
  disjoint G g
  disjoint h i
  disjoint h j
  disjoint h x
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G x
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint Y a
  disjoint Y j
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a k
  disjoint a l
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c x
  disjoint c y
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d x
  disjoint d y
  disjoint e f
  disjoint e g
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e x
  disjoint e y
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g l
  disjoint g y
  disjoint i k
  disjoint i l
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint b h
  disjoint G b
  disjoint c h
  disjoint G c
  disjoint d h
  disjoint G d
  disjoint e h
  disjoint G e
  disjoint f h
  disjoint G f
  disjoint B a
  disjoint B b
  disjoint F c
  disjoint F e
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y e
  assert |- ( ( ph /\ A e. _om ) -> ( ( Y ` A ) : _om -1-1-> _V /\ U. ran ( Y ` A ) C_ G ) )

  proof
    cA
    com
    wcel
    wph
    com
    cvv
    cA
    cY
    cfv
    #
    wf1
    #
    @0
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    wph
    com
    cvv
    va
    cv
    #
    cY
    cfv
    #
    wf1
    #
    @7
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    wi
    wph
    com
    cvv
    c0
    cY
    cfv
    #
    wf1
    #
    @13
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    wi
    wph
    com
    cvv
    vb
    cv
    #
    cY
    cfv
    #
    wf1
    #
    @20
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    wi
    wph
    com
    cvv
    @19
    csuc
    #
    cY
    cfv
    #
    wf1
    #
    @27
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    wi
    wph
    @5
    wi
    va
    vb
    cA
    @6
    c0
    wceq
    #
    @12
    @18
    wph
    @33
    @8
    @14
    @11
    @17
    @33
    @7
    @13
    wceq
    @8
    @14
    wb
    @6
    c0
    cY
    fveq2
    #
    com
    cvv
    @7
    @13
    f1eq1
    syl
    @33
    @10
    @16
    cG
    @33
    @9
    @15
    @33
    @7
    @13
    @34
    rneqd
    unieqd
    sseq1d
    anbi12d
    imbi2d
    @6
    @19
    wceq
    #
    @12
    @25
    wph
    @35
    @8
    @21
    @11
    @24
    @35
    @7
    @20
    wceq
    @8
    @21
    wb
    @6
    @19
    cY
    fveq2
    #
    com
    cvv
    @7
    @20
    f1eq1
    syl
    @35
    @10
    @23
    cG
    @35
    @9
    @22
    @35
    @7
    @20
    @36
    rneqd
    unieqd
    sseq1d
    anbi12d
    imbi2d
    @6
    @26
    wceq
    #
    @12
    @32
    wph
    @37
    @8
    @28
    @11
    @31
    @37
    @7
    @27
    wceq
    @8
    @28
    wb
    @6
    @26
    cY
    fveq2
    #
    com
    cvv
    @7
    @27
    f1eq1
    syl
    @37
    @10
    @30
    cG
    @37
    @9
    @29
    @37
    @7
    @27
    @38
    rneqd
    unieqd
    sseq1d
    anbi12d
    imbi2d
    @6
    cA
    wceq
    #
    @12
    @5
    wph
    @39
    @8
    @1
    @11
    @4
    @39
    @7
    @0
    wceq
    @8
    @1
    wb
    @6
    cA
    cY
    fveq2
    #
    com
    cvv
    @7
    @0
    f1eq1
    syl
    @39
    @10
    @3
    cG
    @39
    @9
    @2
    @39
    @7
    @0
    @40
    rneqd
    unieqd
    sseq1d
    anbi12d
    imbi2d
    wph
    com
    cvv
    vh
    cv
    #
    wf1
    #
    @41
    crn
    #
    cuni
    #
    cG
    wss
    #
    @18
    fin23lem.f
    fin23lem.g
    @14
    @42
    @17
    @45
    @13
    @41
    wceq
    @14
    @42
    wb
    @13
    c0
    vi
    cv
    #
    @41
    crdg
    com
    cres
    #
    cfv
    #
    @41
    c0
    cY
    @47
    fin23lem.i
    fveq1i
    @41
    cvv
    wcel
    @48
    @41
    wceq
    vh
    vex
    @41
    cvv
    @46
    fr0g
    ax-mp
    eqtri
    #
    com
    cvv
    @13
    @41
    f1eq1
    ax-mp
    @16
    @44
    cG
    @15
    @43
    @13
    @41
    @49
    rneqi
    unieqi
    sseq1i
    anbi12i
    sylanbrc
    @19
    com
    wcel
    #
    wph
    @25
    @32
    @50
    wph
    @25
    @32
    @50
    wph
    @25
    w3a
    @32
    com
    cvv
    @20
    @46
    cfv
    #
    wf1
    #
    @51
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    wph
    @25
    @56
    @50
    wph
    @25
    wa
    @52
    @54
    @23
    wpss
    #
    wa
    #
    @56
    wph
    @25
    @58
    wph
    com
    cvv
    vj
    cv
    #
    wf1
    #
    @59
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    com
    cvv
    @59
    @46
    cfv
    #
    wf1
    #
    @65
    crn
    #
    cuni
    #
    @62
    wpss
    #
    wa
    #
    wi
    #
    vj
    wal
    @25
    @58
    wi
    #
    fin23lem.h
    @71
    @72
    vj
    @20
    @19
    cY
    fvex
    @59
    @20
    wceq
    #
    @64
    @25
    @70
    @58
    @73
    @60
    @21
    @63
    @24
    com
    cvv
    @59
    @20
    f1eq1
    @73
    @62
    @23
    cG
    @73
    @61
    @22
    @59
    @20
    rneq
    unieqd
    #
    sseq1d
    anbi12d
    @73
    @66
    @52
    @69
    @57
    @73
    @65
    @51
    wceq
    @66
    @52
    wb
    @59
    @20
    @46
    fveq2
    #
    com
    cvv
    @65
    @51
    f1eq1
    syl
    @73
    @68
    @54
    @62
    @23
    @73
    @67
    @53
    @73
    @65
    @51
    @75
    rneqd
    unieqd
    @74
    psseq12d
    anbi12d
    imbi12d
    spcv
    syl
    imp
    @24
    @58
    @56
    wi
    wph
    @21
    @24
    @57
    @55
    @52
    @57
    @24
    @55
    @57
    @54
    @23
    wss
    @24
    @55
    @54
    @23
    pssss
    @54
    @23
    cG
    sstr
    sylan
    expcom
    anim2d
    ad2antll
    mpd
    3adant1
    @50
    wph
    @32
    @56
    wb
    #
    @25
    @50
    @27
    @51
    wceq
    #
    @76
    @50
    @26
    @47
    cfv
    @19
    @47
    cfv
    #
    @46
    cfv
    @27
    @51
    @41
    @19
    @46
    frsuc
    @26
    cY
    @47
    fin23lem.i
    fveq1i
    @20
    @78
    @46
    @19
    cY
    @47
    fin23lem.i
    fveq1i
    fveq2i
    3eqtr4g
    @77
    @28
    @52
    @31
    @55
    com
    cvv
    @27
    @51
    f1eq1
    @77
    @30
    @54
    cG
    @77
    @29
    @53
    @27
    @51
    rneq
    unieqd
    sseq1d
    anbi12d
    syl
    3ad2ant1
    mpbird
    3exp
    a2d
    finds
    impcom
end
