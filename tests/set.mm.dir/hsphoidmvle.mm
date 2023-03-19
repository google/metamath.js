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
include "min1.mm"
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
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "hsphoival.mm"
include "eldifbd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "adantr.mm"
include "fprodsplit1.mm"
include "wf.mm"
include "cun.mm"
include "wn.mm"
include "syl6eleq.mm"
include "eldifn.mm"
include "elunnel2.mm"
include "iftrued.mm"
include "prodeq2dv.mm"
include "3eqtrd.mm"
include "hoidmvval.mm"
include "neneqd.mm"
include "breq12d.mm"
include "mpbird.mm"

theorem hsphoidmvle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume hsphoidmvle.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hsphoidmvle.x: |- ( ph -> X e. Fin )
  assume hsphoidmvle.z: |- ( ph -> Z e. ( X \ Y ) )
  assume hsphoidmvle.y: |- X = ( Y u. { Z } )
  assume hsphoidmvle.c: |- ( ph -> C e. RR )
  assume hsphoidmvle.h: |- H = ( x e. RR |-> ( c e. ( RR ^m X ) |-> ( j e. X |-> if ( j e. Y , ( c ` j ) , if ( ( c ` j ) <_ x , ( c ` j ) , x ) ) ) ) )
  assume hsphoidmvle.a: |- ( ph -> A : X --> RR )
  assume hsphoidmvle.b: |- ( ph -> B : X --> RR )

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
  assert |- ( ph -> ( A ( L ` X ) ( ( H ` C ) ` B ) ) <_ ( A ( L ` X ) B ) )

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
    @5
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
    @12
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
    @4
    @5
    cico
    co
    #
    cvol
    cfv
    #
    @17
    cmul
    co
    #
    cle
    wbr
    wph
    @9
    @20
    @17
    wph
    @4
    cr
    wcel
    #
    @7
    cr
    wcel
    @9
    cr
    wcel
    wph
    cX
    cr
    cZ
    cA
    hsphoidmvle.a
    wph
    cZ
    cX
    cY
    hsphoidmvle.z
    eldifad
    #
    ffvelrnd
    #
    wph
    @6
    @5
    cC
    cr
    wph
    cX
    cr
    cZ
    cB
    hsphoidmvle.b
    @23
    ffvelrnd
    #
    hsphoidmvle.c
    ifcld
    #
    @4
    @7
    volicore
    syl2anc
    wph
    @22
    @5
    cr
    wcel
    #
    @20
    cr
    wcel
    @24
    @25
    @4
    @5
    volicore
    syl2anc
    wph
    @11
    @16
    vk
    wph
    cX
    cfn
    wcel
    #
    @11
    cX
    wss
    @11
    cfn
    wcel
    hsphoidmvle.x
    wph
    cX
    @10
    difssd
    cX
    @11
    ssfi
    syl2anc
    #
    wph
    @12
    @11
    wcel
    #
    @12
    cX
    wcel
    #
    @16
    cr
    wcel
    #
    @30
    @31
    wph
    @12
    cX
    @10
    eldifi
    #
    adantl
    #
    wph
    @31
    wa
    #
    @13
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    @32
    wph
    cX
    cr
    @12
    cA
    hsphoidmvle.a
    ffvelrnda
    #
    wph
    cX
    cr
    @12
    cB
    hsphoidmvle.b
    ffvelrnda
    #
    @13
    @14
    volicore
    syl2anc
    #
    syldan
    #
    fprodrecl
    wph
    @11
    @16
    vk
    wph
    vk
    nfv
    @29
    @41
    wph
    @30
    wa
    #
    @15
    cvol
    cdm
    #
    wcel
    #
    cc0
    @16
    cle
    wbr
    @42
    @36
    @14
    cxr
    wcel
    @44
    wph
    @30
    @31
    @36
    @34
    @38
    syldan
    @42
    @14
    wph
    @30
    @31
    @37
    @34
    @39
    syldan
    rexrd
    @13
    @14
    icombl
    syl2anc
    @15
    volge0
    syl
    fprodge0
    wph
    @8
    @43
    wcel
    #
    @19
    @43
    wcel
    #
    @8
    @19
    wss
    #
    @9
    @20
    cle
    wbr
    wph
    @22
    @7
    cxr
    wcel
    @45
    @24
    wph
    @7
    @26
    rexrd
    @4
    @7
    icombl
    syl2anc
    wph
    @22
    @5
    cxr
    wcel
    #
    @46
    @24
    wph
    @5
    @25
    rexrd
    #
    @4
    @5
    icombl
    syl2anc
    wph
    @4
    cxr
    wcel
    @48
    @4
    @4
    cle
    wbr
    @7
    @5
    cle
    wbr
    #
    @47
    wph
    @4
    @24
    rexrd
    @49
    wph
    @4
    @24
    leidd
    wph
    @27
    cC
    cr
    wcel
    #
    @50
    @25
    hsphoidmvle.c
    @5
    cC
    min1
    syl2anc
    @4
    @5
    @4
    @7
    icossico
    syl22anc
    @8
    @19
    volss
    syl3anc
    lemul1ad
    wph
    @2
    @18
    @3
    @21
    cle
    wph
    @2
    cX
    @13
    @12
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
    @9
    @11
    @54
    vk
    cprod
    #
    cmul
    co
    @18
    wph
    vx
    cA
    @0
    vk
    cL
    cX
    va
    vb
    hsphoidmvle.l
    hsphoidmvle.x
    wph
    cZ
    cX
    wcel
    cX
    c0
    wne
    @23
    cX
    cZ
    ne0i
    syl
    #
    hsphoidmvle.a
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
    hsphoidmvle.h
    hsphoidmvle.c
    hsphoidmvle.x
    hsphoidmvle.b
    hsphoif
    #
    hoidmvn0val
    wph
    cX
    @54
    cZ
    @9
    vk
    hsphoidmvle.x
    @35
    @54
    @35
    @36
    @52
    cr
    wcel
    @54
    cr
    wcel
    @38
    wph
    cX
    cr
    @12
    @0
    @57
    ffvelrnda
    @13
    @52
    volicore
    syl2anc
    recnd
    @23
    wph
    @12
    cZ
    wceq
    #
    wa
    @54
    @4
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
    @9
    @58
    @54
    @61
    wceq
    wph
    @58
    @53
    @60
    cvol
    @58
    @13
    @4
    @52
    @59
    cico
    @12
    cZ
    cA
    fveq2
    #
    @12
    cZ
    @0
    fveq2
    oveq12d
    fveq2d
    adantl
    wph
    @61
    @9
    wceq
    @58
    wph
    @60
    @8
    cvol
    wph
    @59
    @7
    @4
    cico
    wph
    @59
    cZ
    cY
    wcel
    #
    @5
    @7
    cif
    @7
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
    hsphoidmvle.h
    hsphoidmvle.c
    hsphoidmvle.x
    hsphoidmvle.b
    @23
    hsphoival
    wph
    @63
    @5
    @7
    wph
    cZ
    cX
    cY
    hsphoidmvle.z
    eldifbd
    iffalsed
    eqtrd
    oveq2d
    fveq2d
    adantr
    eqtrd
    fprodsplit1
    wph
    @55
    @17
    @9
    cmul
    wph
    @11
    @54
    @16
    vk
    @42
    @53
    @15
    cvol
    @42
    @52
    @14
    @13
    cico
    @42
    @52
    @12
    cY
    wcel
    #
    @14
    @14
    cC
    cle
    wbr
    @14
    cC
    cif
    #
    cif
    @14
    @42
    vx
    cC
    cB
    vj
    cH
    @12
    cfn
    cX
    cY
    vc
    hsphoidmvle.h
    wph
    @51
    @30
    hsphoidmvle.c
    adantr
    wph
    @28
    @30
    hsphoidmvle.x
    adantr
    wph
    cX
    cr
    cB
    wf
    @30
    hsphoidmvle.b
    adantr
    @34
    hsphoival
    @42
    @64
    @14
    @65
    @30
    @64
    wph
    @30
    @12
    cY
    @10
    cun
    #
    wcel
    @12
    @10
    wcel
    wn
    @64
    @30
    @12
    cX
    @66
    @33
    hsphoidmvle.y
    syl6eleq
    @12
    cX
    @10
    eldifn
    @12
    cY
    @10
    elunnel2
    syl2anc
    adantl
    iftrued
    eqtrd
    oveq2d
    fveq2d
    prodeq2dv
    oveq2d
    3eqtrd
    wph
    @3
    cX
    c0
    wceq
    #
    cc0
    cX
    @16
    vk
    cprod
    #
    cif
    @68
    @21
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hsphoidmvle.l
    hsphoidmvle.a
    hsphoidmvle.b
    hsphoidmvle.x
    hoidmvval
    wph
    @67
    cc0
    @68
    wph
    cX
    c0
    @56
    neneqd
    iffalsed
    wph
    cX
    @16
    cZ
    @20
    vk
    hsphoidmvle.x
    @35
    @16
    @40
    recnd
    @23
    @58
    @16
    @20
    wceq
    wph
    @58
    @15
    @19
    cvol
    @58
    @13
    @4
    @14
    @5
    cico
    @62
    @12
    cZ
    cB
    fveq2
    oveq12d
    fveq2d
    adantl
    fprodsplit1
    3eqtrd
    breq12d
    mpbird
end
