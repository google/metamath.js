include "cs3.mm"
include "cv.mm"
include "cc0.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfv.mm"
include "ccgrg.mm"
include "wbr.mm"
include "c2.mm"
include "w3a.mm"
include "wrex.mm"
include "copab.mm"
include "ccgra.mm"
include "wb.mm"
include "wceq.mm"
include "simpl.mm"
include "eqidd.mm"
include "simpr.mm"
include "fveq1d.mm"
include "s3eqd.mm"
include "breq12d.mm"
include "fveq2d.mm"
include "breq123d.mm"
include "3anbi123d.mm"
include "2rexbidv.mm"
include "eqid.mm"
include "brab2a.mm"
include "a1i.mm"
include "s3fv1.mm"
include "syl.mm"
include "adantr.mm"
include "breq2d.mm"
include "s3fv0.mm"
include "s3fv2.mm"
include "2rexbidva.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "cstrkg.mm"
include "cvv.mm"
include "elex.mm"
include "chlg.mm"
include "wsbc.mm"
include "cbs.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "fveq12d.mm"
include "breqd.mm"
include "3anbi23d.mm"
include "bicomd.mm"
include "rexeqbidv.mm"
include "sbcie2s.mm"
include "opabbidv.mm"
include "fveq2.mm"
include "3anbi1d.mm"
include "rexbidv.mm"
include "eqtrd.mm"
include "df-cgra.mm"
include "cxp.mm"
include "ovex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "3syl.mm"
include "cword.mm"
include "chash.mm"
include "s3cld.mm"
include "s3len.mm"
include "jca.mm"
include "cn0.mm"
include "fvex.mm"
include "eqeltri.mm"
include "3nn0.mm"
include "wrdmap.mm"
include "mp2an.mm"
include "sylib.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem iscgra
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  assume iscgra.p: |- P = ( Base ` G )
  assume iscgra.i: |- I = ( Itv ` G )
  assume iscgra.k: |- K = ( hlG ` G )
  assume iscgra.g: |- ( ph -> G e. TarskiG )
  assume iscgra.a: |- ( ph -> A e. P )
  assume iscgra.b: |- ( ph -> B e. P )
  assume iscgra.c: |- ( ph -> C e. P )
  assume iscgra.d: |- ( ph -> D e. P )
  assume iscgra.e: |- ( ph -> E e. P )
  assume iscgra.f: |- ( ph -> F e. P )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint F x
  disjoint F y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint P x
  disjoint P y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint E a
  disjoint E b
  disjoint F a
  disjoint F b
  disjoint K a
  disjoint K b
  disjoint K g
  disjoint K k
  disjoint K p
  disjoint a g
  disjoint a k
  disjoint a p
  disjoint b g
  disjoint b k
  disjoint b p
  disjoint g k
  disjoint g p
  disjoint g x
  disjoint g y
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint p x
  disjoint p y
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G k
  disjoint G p
  disjoint I a
  disjoint I b
  disjoint I g
  disjoint I k
  disjoint I p
  disjoint P a
  disjoint P b
  disjoint P g
  disjoint P k
  disjoint P p
  assert |- ( ph -> ( <" A B C "> ( cgrA ` G ) <" D E F "> <-> E. x e. P E. y e. P ( <" A B C "> ( cgrG ` G ) <" x E y "> /\ x ( K ` E ) D /\ y ( K ` E ) F ) ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cD
    cE
    cF
    cs3
    #
    va
    cv
    #
    cP
    cc0
    c3
    cfzo
    co
    #
    cmap
    co
    #
    wcel
    #
    vb
    cv
    #
    @4
    wcel
    #
    wa
    #
    @2
    vx
    cv
    #
    c1
    @6
    cfv
    #
    vy
    cv
    #
    cs3
    #
    cG
    ccgrg
    cfv
    #
    wbr
    #
    @9
    cc0
    @6
    cfv
    #
    @10
    cK
    cfv
    #
    wbr
    #
    @11
    c2
    @6
    cfv
    #
    @16
    wbr
    #
    w3a
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    wbr
    #
    @0
    @4
    wcel
    #
    @1
    @4
    wcel
    #
    wa
    #
    @0
    @9
    cE
    @11
    cs3
    #
    @13
    wbr
    #
    @9
    cD
    cE
    cK
    cfv
    #
    wbr
    #
    @11
    cF
    @31
    wbr
    #
    w3a
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    wa
    #
    @0
    @1
    cG
    ccgra
    cfv
    #
    wbr
    @35
    wph
    @25
    @28
    @0
    @9
    c1
    @1
    cfv
    #
    @11
    cs3
    #
    @13
    wbr
    #
    @9
    cc0
    @1
    cfv
    #
    @38
    cK
    cfv
    #
    wbr
    #
    @11
    c2
    @1
    cfv
    #
    @42
    wbr
    #
    w3a
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    wa
    #
    @36
    @25
    @48
    wb
    wph
    @22
    @47
    va
    vb
    @0
    @1
    @4
    @4
    @24
    @2
    @0
    wceq
    #
    @6
    @1
    wceq
    #
    wa
    #
    @20
    @46
    vx
    vy
    cP
    cP
    @51
    @14
    @40
    @17
    @43
    @19
    @45
    @51
    @2
    @0
    @12
    @39
    @13
    @49
    @50
    simpl
    @51
    @9
    @10
    @11
    @11
    @9
    @38
    @51
    @9
    eqidd
    #
    @51
    c1
    @6
    @1
    @49
    @50
    simpr
    #
    fveq1d
    #
    @51
    @11
    eqidd
    #
    s3eqd
    breq12d
    @51
    @9
    @9
    @15
    @41
    @16
    @42
    @52
    @51
    @10
    @38
    cK
    @54
    fveq2d
    #
    @51
    cc0
    @6
    @1
    @53
    fveq1d
    breq123d
    @51
    @11
    @11
    @18
    @44
    @16
    @42
    @55
    @56
    @51
    c2
    @6
    @1
    @53
    fveq1d
    breq123d
    3anbi123d
    2rexbidv
    @24
    eqid
    brab2a
    a1i
    wph
    @47
    @35
    @28
    wph
    @46
    @34
    vx
    vy
    cP
    cP
    wph
    @9
    cP
    wcel
    @11
    cP
    wcel
    wa
    #
    wa
    #
    @40
    @30
    @43
    @32
    @45
    @33
    @58
    @39
    @29
    @0
    @13
    @58
    @9
    @38
    @11
    @11
    @9
    cE
    @58
    @9
    eqidd
    #
    wph
    @38
    cE
    wceq
    #
    @57
    wph
    cE
    cP
    wcel
    @60
    iscgra.e
    cD
    cE
    cF
    cP
    s3fv1
    syl
    adantr
    #
    @58
    @11
    eqidd
    #
    s3eqd
    breq2d
    @58
    @9
    @9
    @41
    cD
    @42
    @31
    @59
    @58
    @38
    cE
    cK
    @61
    fveq2d
    #
    wph
    @41
    cD
    wceq
    #
    @57
    wph
    cD
    cP
    wcel
    @64
    iscgra.d
    cD
    cE
    cF
    cP
    s3fv0
    syl
    adantr
    breq123d
    @58
    @11
    @11
    @44
    cF
    @42
    @31
    @62
    @63
    wph
    @44
    cF
    wceq
    #
    @57
    wph
    cF
    cP
    wcel
    @65
    iscgra.f
    cD
    cE
    cF
    cP
    s3fv2
    syl
    adantr
    breq123d
    3anbi123d
    2rexbidva
    anbi2d
    bitrd
    wph
    @37
    @24
    @0
    @1
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    @37
    @24
    wceq
    iscgra.g
    cG
    cstrkg
    elex
    vg
    cG
    @2
    vp
    cv
    #
    @3
    cmap
    co
    #
    wcel
    #
    @6
    @67
    wcel
    #
    wa
    #
    @2
    @12
    vg
    cv
    #
    ccgrg
    cfv
    #
    wbr
    #
    @9
    @15
    @10
    vk
    cv
    #
    cfv
    #
    wbr
    #
    @11
    @18
    @75
    wbr
    #
    w3a
    #
    vy
    @66
    wrex
    #
    vx
    @66
    wrex
    #
    wa
    #
    vk
    @71
    chlg
    cfv
    wsbc
    vp
    @71
    cbs
    cfv
    wsbc
    #
    va
    vb
    copab
    #
    @24
    cvv
    ccgra
    @71
    cG
    wceq
    #
    @83
    @8
    @73
    @17
    @19
    w3a
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    wa
    #
    va
    vb
    copab
    @24
    @84
    @82
    @88
    va
    vb
    @88
    @81
    vg
    cP
    cK
    cbs
    chlg
    cG
    vp
    vk
    iscgra.p
    iscgra.k
    @66
    cP
    wceq
    #
    @74
    cK
    wceq
    #
    wa
    #
    @8
    @70
    @87
    @80
    @91
    @5
    @68
    @7
    @69
    @91
    @4
    @67
    @2
    @91
    cP
    @66
    @3
    cmap
    @91
    @66
    cP
    @89
    @90
    simpl
    eqcomd
    #
    oveq1d
    #
    eleq2d
    @91
    @4
    @67
    @6
    @93
    eleq2d
    anbi12d
    @91
    @86
    @79
    vx
    cP
    @66
    @92
    @91
    @85
    @78
    vy
    cP
    @66
    @92
    @91
    @78
    @85
    @91
    @76
    @17
    @77
    @19
    @73
    @91
    @75
    @16
    @9
    @15
    @91
    @10
    @10
    @74
    cK
    @89
    @90
    simpr
    @91
    @10
    eqidd
    fveq12d
    #
    breqd
    @91
    @75
    @16
    @11
    @18
    @94
    breqd
    3anbi23d
    bicomd
    rexeqbidv
    rexeqbidv
    anbi12d
    sbcie2s
    opabbidv
    @84
    @88
    @23
    va
    vb
    @84
    @87
    @22
    @8
    @84
    @86
    @21
    vx
    cP
    @84
    @85
    @20
    vy
    cP
    @84
    @73
    @14
    @17
    @19
    @84
    @72
    @13
    @2
    @12
    @71
    cG
    ccgrg
    fveq2
    breqd
    3anbi1d
    rexbidv
    rexbidv
    anbi2d
    opabbidv
    eqtrd
    vx
    vy
    vg
    vk
    vp
    va
    vb
    df-cgra
    @24
    @4
    @4
    cxp
    @4
    @4
    cP
    @3
    cmap
    ovex
    #
    @95
    xpex
    @22
    va
    vb
    @4
    @4
    opabssxp
    ssexi
    fvmpt
    3syl
    breqd
    wph
    @28
    @35
    wph
    @26
    @27
    wph
    @0
    cP
    cword
    #
    wcel
    #
    @0
    chash
    cfv
    c3
    wceq
    #
    wa
    #
    @26
    wph
    @97
    @98
    wph
    cA
    cB
    cC
    cP
    iscgra.a
    iscgra.b
    iscgra.c
    s3cld
    @98
    wph
    cA
    cB
    cC
    s3len
    a1i
    jca
    cP
    cvv
    wcel
    #
    c3
    cn0
    wcel
    #
    @99
    @26
    wb
    cP
    cG
    cbs
    cfv
    cvv
    iscgra.p
    cG
    cbs
    fvex
    eqeltri
    #
    3nn0
    c3
    cP
    @0
    cvv
    wrdmap
    mp2an
    sylib
    wph
    @1
    @96
    wcel
    #
    @1
    chash
    cfv
    c3
    wceq
    #
    wa
    #
    @27
    wph
    @103
    @104
    wph
    cD
    cE
    cF
    cP
    iscgra.d
    iscgra.e
    iscgra.f
    s3cld
    @104
    wph
    cD
    cE
    cF
    s3len
    a1i
    jca
    @100
    @101
    @105
    @27
    wb
    @102
    3nn0
    c3
    cP
    @1
    cvv
    wrdmap
    mp2an
    sylib
    jca
    biantrurd
    3bitr4d
end
