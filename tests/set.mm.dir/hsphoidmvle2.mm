include "cfv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cico.mm"
include "cvol.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cprod.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "eldifad.mm"
include "ffvelrnd.mm"
include "ifcld.mm"
include "volicore.mm"
include "syl2anc.mm"
include "cfn.mm"
include "wss.mm"
include "difssd.mm"
include "ssfi.mm"
include "eldifi.mm"
include "adantl.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "fprodrecl.mm"
include "nfv.mm"
include "cdm.mm"
include "cc0.mm"
include "cxr.mm"
include "rexrd.mm"
include "icombl.mm"
include "volge0.mm"
include "syl.mm"
include "fprodge0.mm"
include "leidd.mm"
include "adantr.mm"
include "wceq.mm"
include "iftrue.mm"
include "simpr.mm"
include "letrd.mm"
include "iftrued.mm"
include "breq12d.mm"
include "mpbird.mm"
include "wn.mm"
include "clt.mm"
include "simpl.mm"
include "ltnled.mm"
include "ltled.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "ad2antrr.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "breq1d.mm"
include "icossico.mm"
include "syl22anc.mm"
include "volss.mm"
include "syl3anc.mm"
include "lemul1ad.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "hsphoif.mm"
include "hoidmvn0val.mm"
include "recnd.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "hsphoival.mm"
include "eldifbd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fprodsplit1.mm"
include "wf.mm"
include "cun.mm"
include "syl6eleq.mm"
include "eldifn.mm"
include "elunnel2.mm"
include "prodeq2dv.mm"
include "3eqtrd.mm"

theorem hsphoidmvle2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cH: class H
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume hsphoidmvle2.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hsphoidmvle2.x: |- ( ph -> X e. Fin )
  assume hsphoidmvle2.z: |- ( ph -> Z e. ( X \ Y ) )
  assume hsphoidmvle2.y: |- X = ( Y u. { Z } )
  assume hsphoidmvle2.c: |- ( ph -> C e. RR )
  assume hsphoidmvle2.d: |- ( ph -> D e. RR )
  assume hsphoidmvle2.e: |- ( ph -> C <_ D )
  assume hsphoidmvle2.h: |- H = ( x e. RR |-> ( c e. ( RR ^m X ) |-> ( j e. X |-> if ( j e. Y , ( c ` j ) , if ( ( c ` j ) <_ x , ( c ` j ) , x ) ) ) ) )
  assume hsphoidmvle2.a: |- ( ph -> A : X --> RR )
  assume hsphoidmvle2.b: |- ( ph -> B : X --> RR )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint B c
  disjoint B j
  disjoint c j
  disjoint c k
  disjoint j k
  disjoint C a
  disjoint C b
  disjoint C k
  disjoint C x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint C c
  disjoint C j
  disjoint c x
  disjoint j x
  disjoint D a
  disjoint D b
  disjoint D k
  disjoint D x
  disjoint D c
  disjoint D j
  disjoint H a
  disjoint H b
  disjoint H k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint X c
  disjoint X j
  disjoint Y c
  disjoint Y j
  disjoint Y x
  disjoint Z c
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint c ph
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( A ( L ` X ) ( ( H ` C ) ` B ) ) <_ ( A ( L ` X ) ( ( H ` D ) ` B ) ) )

  proof
    wph
    cA
    cB
    cC
    cH
    cfv
    cfv
    #
    cX
    cL
    cfv
    #
    co
    #
    cA
    cB
    cD
    cH
    cfv
    cfv
    #
    @1
    co
    #
    cle
    wbr
    cZ
    cA
    cfv
    #
    cZ
    cB
    cfv
    #
    cC
    cle
    wbr
    #
    @6
    cC
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cX
    cZ
    csn
    #
    cdif
    #
    vk
    cv
    #
    cA
    cfv
    #
    @13
    cB
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmul
    co
    #
    @5
    @6
    cD
    cle
    wbr
    #
    @6
    cD
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    @18
    cmul
    co
    #
    cle
    wbr
    wph
    @10
    @23
    @18
    wph
    @5
    cr
    wcel
    #
    @8
    cr
    wcel
    @10
    cr
    wcel
    wph
    cX
    cr
    cZ
    cA
    hsphoidmvle2.a
    wph
    cZ
    cX
    cY
    hsphoidmvle2.z
    eldifad
    #
    ffvelrnd
    #
    wph
    @7
    @6
    cC
    cr
    wph
    cX
    cr
    cZ
    cB
    hsphoidmvle2.b
    @26
    ffvelrnd
    #
    hsphoidmvle2.c
    ifcld
    #
    @5
    @8
    volicore
    syl2anc
    wph
    @25
    @21
    cr
    wcel
    @23
    cr
    wcel
    @27
    wph
    @20
    @6
    cD
    cr
    @28
    hsphoidmvle2.d
    ifcld
    #
    @5
    @21
    volicore
    syl2anc
    wph
    @12
    @17
    vk
    wph
    cX
    cfn
    wcel
    #
    @12
    cX
    wss
    @12
    cfn
    wcel
    hsphoidmvle2.x
    wph
    cX
    @11
    difssd
    cX
    @12
    ssfi
    syl2anc
    #
    wph
    @13
    @12
    wcel
    #
    @13
    cX
    wcel
    #
    @17
    cr
    wcel
    #
    @33
    @34
    wph
    @13
    cX
    @11
    eldifi
    #
    adantl
    #
    wph
    @34
    wa
    #
    @14
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @35
    wph
    cX
    cr
    @13
    cA
    hsphoidmvle2.a
    ffvelrnda
    #
    wph
    cX
    cr
    @13
    cB
    hsphoidmvle2.b
    ffvelrnda
    #
    @14
    @15
    volicore
    syl2anc
    syldan
    #
    fprodrecl
    wph
    @12
    @17
    vk
    wph
    vk
    nfv
    @32
    @43
    wph
    @33
    wa
    #
    @16
    cvol
    cdm
    #
    wcel
    #
    cc0
    @17
    cle
    wbr
    @44
    @39
    @15
    cxr
    wcel
    @46
    wph
    @33
    @34
    @39
    @37
    @41
    syldan
    @44
    @15
    wph
    @33
    @34
    @40
    @37
    @42
    syldan
    rexrd
    @14
    @15
    icombl
    syl2anc
    @16
    volge0
    syl
    fprodge0
    wph
    @9
    @45
    wcel
    #
    @22
    @45
    wcel
    #
    @9
    @22
    wss
    #
    @10
    @23
    cle
    wbr
    wph
    @25
    @8
    cxr
    wcel
    @47
    @27
    wph
    @8
    @29
    rexrd
    @5
    @8
    icombl
    syl2anc
    wph
    @25
    @21
    cxr
    wcel
    #
    @48
    @27
    wph
    @21
    @30
    rexrd
    #
    @5
    @21
    icombl
    syl2anc
    wph
    @5
    cxr
    wcel
    @50
    @5
    @5
    cle
    wbr
    @8
    @21
    cle
    wbr
    #
    @49
    wph
    @5
    @27
    rexrd
    @51
    wph
    @5
    @27
    leidd
    wph
    @7
    @52
    wph
    @7
    wa
    #
    @52
    @6
    @6
    cle
    wbr
    #
    wph
    @54
    @7
    wph
    @6
    @28
    leidd
    adantr
    @53
    @8
    @6
    @21
    @6
    cle
    @7
    @8
    @6
    wceq
    wph
    @7
    @6
    cC
    iftrue
    adantl
    @53
    @20
    @6
    cD
    @53
    @6
    cC
    cD
    wph
    @6
    cr
    wcel
    #
    @7
    @28
    adantr
    wph
    cC
    cr
    wcel
    #
    @7
    hsphoidmvle2.c
    adantr
    wph
    cD
    cr
    wcel
    #
    @7
    hsphoidmvle2.d
    adantr
    wph
    @7
    simpr
    wph
    cC
    cD
    cle
    wbr
    #
    @7
    hsphoidmvle2.e
    adantr
    letrd
    iftrued
    breq12d
    mpbird
    wph
    @7
    wn
    #
    wa
    #
    @52
    cC
    @21
    cle
    wbr
    #
    @60
    wph
    cC
    @6
    clt
    wbr
    #
    @61
    wph
    @59
    simpl
    #
    @60
    @62
    @59
    wph
    @59
    simpr
    @60
    cC
    @6
    @60
    wph
    @56
    @63
    hsphoidmvle2.c
    syl
    @60
    wph
    @55
    @63
    @28
    syl
    ltnled
    mpbird
    wph
    @62
    wa
    #
    @20
    @61
    @64
    @20
    wa
    cC
    @6
    @21
    cle
    @64
    cC
    @6
    cle
    wbr
    @20
    @64
    cC
    @6
    wph
    @56
    @62
    hsphoidmvle2.c
    adantr
    wph
    @55
    @62
    @28
    adantr
    wph
    @62
    simpr
    ltled
    adantr
    @20
    @6
    @21
    wceq
    @64
    @20
    @21
    @6
    @20
    @6
    cD
    iftrue
    eqcomd
    adantl
    breqtrd
    @64
    @20
    wn
    #
    wa
    cC
    cD
    @21
    cle
    wph
    @58
    @62
    @65
    hsphoidmvle2.e
    ad2antrr
    @65
    cD
    @21
    wceq
    @64
    @65
    @21
    cD
    @20
    @6
    cD
    iffalse
    eqcomd
    adantl
    breqtrd
    pm2.61dan
    syl2anc
    @60
    @8
    cC
    @21
    cle
    @59
    @8
    cC
    wceq
    wph
    @7
    @6
    cC
    iffalse
    adantl
    breq1d
    mpbird
    pm2.61dan
    @5
    @21
    @5
    @8
    icossico
    syl22anc
    @9
    @22
    volss
    syl3anc
    lemul1ad
    wph
    @2
    @19
    @4
    @24
    cle
    wph
    @2
    cX
    @14
    @13
    @0
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    @10
    @12
    @68
    vk
    cprod
    #
    cmul
    co
    @19
    wph
    vx
    cA
    @0
    vk
    cL
    cX
    va
    vb
    hsphoidmvle2.l
    hsphoidmvle2.x
    wph
    cZ
    cX
    wcel
    cX
    c0
    wne
    @26
    cX
    cZ
    ne0i
    syl
    #
    hsphoidmvle2.a
    wph
    vx
    cC
    cB
    vj
    cH
    cfn
    cX
    cY
    vc
    hsphoidmvle2.h
    hsphoidmvle2.c
    hsphoidmvle2.x
    hsphoidmvle2.b
    hsphoif
    #
    hoidmvn0val
    wph
    cX
    @68
    cZ
    @10
    vk
    hsphoidmvle2.x
    @38
    @68
    @38
    @39
    @66
    cr
    wcel
    @68
    cr
    wcel
    @41
    wph
    cX
    cr
    @13
    @0
    @71
    ffvelrnda
    @14
    @66
    volicore
    syl2anc
    recnd
    @26
    wph
    @13
    cZ
    wceq
    #
    wa
    @68
    @5
    cZ
    @0
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    @10
    @72
    @68
    @75
    wceq
    wph
    @72
    @67
    @74
    cvol
    @72
    @14
    @5
    @66
    @73
    cico
    @13
    cZ
    cA
    fveq2
    #
    @13
    cZ
    @0
    fveq2
    oveq12d
    fveq2d
    adantl
    wph
    @75
    @10
    wceq
    @72
    wph
    @74
    @9
    cvol
    wph
    @73
    @8
    @5
    cico
    wph
    @73
    cZ
    cY
    wcel
    #
    @6
    @8
    cif
    @8
    wph
    vx
    cC
    cB
    vj
    cH
    cZ
    cfn
    cX
    cY
    vc
    hsphoidmvle2.h
    hsphoidmvle2.c
    hsphoidmvle2.x
    hsphoidmvle2.b
    @26
    hsphoival
    wph
    @77
    @6
    @8
    wph
    cZ
    cX
    cY
    hsphoidmvle2.z
    eldifbd
    #
    iffalsed
    eqtrd
    oveq2d
    fveq2d
    adantr
    eqtrd
    fprodsplit1
    wph
    @69
    @18
    @10
    cmul
    wph
    @12
    @68
    @17
    vk
    @44
    @67
    @16
    cvol
    @44
    @66
    @15
    @14
    cico
    @44
    @66
    @13
    cY
    wcel
    #
    @15
    @15
    cC
    cle
    wbr
    @15
    cC
    cif
    #
    cif
    @15
    @44
    vx
    cC
    cB
    vj
    cH
    @13
    cfn
    cX
    cY
    vc
    hsphoidmvle2.h
    wph
    @56
    @33
    hsphoidmvle2.c
    adantr
    wph
    @31
    @33
    hsphoidmvle2.x
    adantr
    #
    wph
    cX
    cr
    cB
    wf
    @33
    hsphoidmvle2.b
    adantr
    #
    @37
    hsphoival
    @44
    @79
    @15
    @80
    @33
    @79
    wph
    @33
    @13
    cY
    @11
    cun
    #
    wcel
    @13
    @11
    wcel
    wn
    @79
    @33
    @13
    cX
    @83
    @36
    hsphoidmvle2.y
    syl6eleq
    @13
    cX
    @11
    eldifn
    @13
    cY
    @11
    elunnel2
    syl2anc
    adantl
    #
    iftrued
    eqtrd
    oveq2d
    fveq2d
    prodeq2dv
    oveq2d
    3eqtrd
    wph
    @4
    cX
    @14
    @13
    @3
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    @5
    cZ
    @3
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    @12
    @87
    vk
    cprod
    #
    cmul
    co
    @24
    wph
    vx
    cA
    @3
    vk
    cL
    cX
    va
    vb
    hsphoidmvle2.l
    hsphoidmvle2.x
    @70
    hsphoidmvle2.a
    wph
    vx
    cD
    cB
    vj
    cH
    cfn
    cX
    cY
    vc
    hsphoidmvle2.h
    hsphoidmvle2.d
    hsphoidmvle2.x
    hsphoidmvle2.b
    hsphoif
    #
    hoidmvn0val
    wph
    cX
    @87
    cZ
    @90
    vk
    hsphoidmvle2.x
    @38
    @87
    @38
    @39
    @85
    cr
    wcel
    @87
    cr
    wcel
    @41
    wph
    cX
    cr
    @13
    @3
    @92
    ffvelrnda
    @14
    @85
    volicore
    syl2anc
    recnd
    @26
    @72
    @87
    @90
    wceq
    wph
    @72
    @86
    @89
    cvol
    @72
    @14
    @5
    @85
    @88
    cico
    @76
    @13
    cZ
    @3
    fveq2
    oveq12d
    fveq2d
    adantl
    fprodsplit1
    wph
    @90
    @23
    @91
    @18
    cmul
    wph
    @89
    @22
    cvol
    wph
    @88
    @21
    @5
    cico
    wph
    @88
    @77
    @6
    @21
    cif
    @21
    wph
    vx
    cD
    cB
    vj
    cH
    cZ
    cfn
    cX
    cY
    vc
    hsphoidmvle2.h
    hsphoidmvle2.d
    hsphoidmvle2.x
    hsphoidmvle2.b
    @26
    hsphoival
    wph
    @77
    @6
    @21
    @78
    iffalsed
    eqtrd
    oveq2d
    fveq2d
    wph
    @12
    @87
    @17
    vk
    @44
    @86
    @16
    cvol
    @44
    @85
    @15
    @14
    cico
    @44
    @85
    @79
    @15
    @15
    cD
    cle
    wbr
    @15
    cD
    cif
    #
    cif
    @15
    @44
    vx
    cD
    cB
    vj
    cH
    @13
    cfn
    cX
    cY
    vc
    hsphoidmvle2.h
    wph
    @57
    @33
    hsphoidmvle2.d
    adantr
    @81
    @82
    @37
    hsphoival
    @44
    @79
    @15
    @93
    @84
    iftrued
    eqtrd
    oveq2d
    fveq2d
    prodeq2dv
    oveq12d
    3eqtrd
    breq12d
    mpbird
end
