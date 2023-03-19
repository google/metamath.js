include "cs3.mm"
include "cleag.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cinag.mm"
include "ccgra.mm"
include "wrex.mm"
include "c1.mm"
include "c2.mm"
include "copab.mm"
include "cstrkg.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "breqd.mm"
include "rexeqbidv.mm"
include "opabbidv.mm"
include "df-leag.mm"
include "cxp.mm"
include "ovex.mm"
include "xpexg.mm"
include "mp2an.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "3syl.mm"
include "wb.mm"
include "simpr.mm"
include "fveq1d.mm"
include "s3eqd.mm"
include "breq2d.mm"
include "simpl.mm"
include "eqidd.mm"
include "breq12d.mm"
include "rexbidv.mm"
include "eqid.mm"
include "brab2a.mm"
include "a1i.mm"
include "s3fv0.mm"
include "syl.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "anbi2d.mm"
include "3bitrd.mm"
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
include "sylib.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem isleag
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume isleag.p: |- P = ( Base ` G )
  assume isleag.g: |- ( ph -> G e. TarskiG )
  assume isleag.a: |- ( ph -> A e. P )
  assume isleag.b: |- ( ph -> B e. P )
  assume isleag.c: |- ( ph -> C e. P )
  assume isleag.d: |- ( ph -> D e. P )
  assume isleag.e: |- ( ph -> E e. P )
  assume isleag.f: |- ( ph -> F e. P )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint E x
  disjoint F x
  disjoint G x
  disjoint P x
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint b x
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
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint a g
  disjoint b g
  disjoint g x
  disjoint P a
  disjoint P b
  disjoint P g
  assert |- ( ph -> ( <" A B C "> ( leA ` G ) <" D E F "> <-> E. x e. P ( x ( inA ` G ) <" D E F "> /\ <" A B C "> ( cgrA ` G ) <" D E x "> ) ) )

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
    cG
    cleag
    cfv
    #
    wbr
    #
    @0
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
    @1
    @5
    wcel
    #
    wa
    #
    vx
    cv
    #
    @1
    cG
    cinag
    cfv
    #
    wbr
    #
    @0
    cD
    cE
    @9
    cs3
    #
    cG
    ccgra
    cfv
    #
    wbr
    #
    wa
    #
    vx
    cP
    wrex
    #
    wa
    #
    @16
    wph
    @3
    @0
    @1
    va
    cv
    #
    @5
    wcel
    #
    vb
    cv
    #
    @5
    wcel
    #
    wa
    #
    @9
    cc0
    @20
    cfv
    #
    c1
    @20
    cfv
    #
    c2
    @20
    cfv
    #
    cs3
    #
    @10
    wbr
    #
    cc0
    @18
    cfv
    #
    c1
    @18
    cfv
    #
    c2
    @18
    cfv
    #
    cs3
    #
    @23
    @24
    @9
    cs3
    #
    @13
    wbr
    #
    wa
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
    @8
    @9
    cc0
    @1
    cfv
    #
    c1
    @1
    cfv
    #
    c2
    @1
    cfv
    #
    cs3
    #
    @10
    wbr
    #
    cc0
    @0
    cfv
    #
    c1
    @0
    cfv
    #
    c2
    @0
    cfv
    #
    cs3
    #
    @39
    @40
    @9
    cs3
    #
    @13
    wbr
    #
    wa
    #
    vx
    cP
    wrex
    #
    wa
    #
    @17
    wph
    @2
    @37
    @0
    @1
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    @2
    @37
    wceq
    isleag.g
    cG
    cstrkg
    elex
    vg
    cG
    @18
    vg
    cv
    #
    cbs
    cfv
    #
    @4
    cmap
    co
    #
    wcel
    #
    @20
    @55
    wcel
    #
    wa
    #
    @9
    @26
    @53
    cinag
    cfv
    #
    wbr
    #
    @31
    @32
    @53
    ccgra
    cfv
    #
    wbr
    #
    wa
    #
    vx
    @54
    wrex
    #
    wa
    #
    va
    vb
    copab
    @37
    cvv
    cleag
    @53
    cG
    wceq
    #
    @65
    @36
    va
    vb
    @66
    @58
    @22
    @64
    @35
    @66
    @56
    @19
    @57
    @21
    @66
    @55
    @5
    @18
    @66
    @54
    cP
    @4
    cmap
    @66
    @54
    cG
    cbs
    cfv
    #
    cP
    @53
    cG
    cbs
    fveq2
    isleag.p
    syl6eqr
    #
    oveq1d
    #
    eleq2d
    @66
    @55
    @5
    @20
    @69
    eleq2d
    anbi12d
    @66
    @63
    @34
    vx
    @54
    cP
    @68
    @66
    @60
    @27
    @62
    @33
    @66
    @59
    @10
    @9
    @26
    @53
    cG
    cinag
    fveq2
    breqd
    @66
    @61
    @13
    @31
    @32
    @53
    cG
    ccgra
    fveq2
    breqd
    anbi12d
    rexeqbidv
    anbi12d
    opabbidv
    vx
    vg
    va
    vb
    df-leag
    @37
    @5
    @5
    cxp
    #
    @5
    cvv
    wcel
    #
    @71
    @70
    cvv
    wcel
    cP
    @4
    cmap
    ovex
    #
    @72
    @5
    @5
    cvv
    cvv
    xpexg
    mp2an
    @35
    va
    vb
    @5
    @5
    opabssxp
    ssexi
    fvmpt
    3syl
    breqd
    @38
    @52
    wb
    wph
    @35
    @51
    va
    vb
    @0
    @1
    @5
    @5
    @37
    @18
    @0
    wceq
    #
    @20
    @1
    wceq
    #
    wa
    #
    @34
    @50
    vx
    cP
    @75
    @27
    @43
    @33
    @49
    @75
    @26
    @42
    @9
    @10
    @75
    @23
    @24
    @25
    @41
    @39
    @40
    @75
    cc0
    @20
    @1
    @73
    @74
    simpr
    #
    fveq1d
    #
    @75
    c1
    @20
    @1
    @76
    fveq1d
    #
    @75
    c2
    @20
    @1
    @76
    fveq1d
    s3eqd
    breq2d
    @75
    @31
    @47
    @32
    @48
    @13
    @75
    @28
    @29
    @30
    @46
    @44
    @45
    @75
    cc0
    @18
    @0
    @73
    @74
    simpl
    #
    fveq1d
    @75
    c1
    @18
    @0
    @79
    fveq1d
    @75
    c2
    @18
    @0
    @79
    fveq1d
    s3eqd
    @75
    @23
    @24
    @9
    @9
    @39
    @40
    @77
    @78
    @75
    @9
    eqidd
    s3eqd
    breq12d
    anbi12d
    rexbidv
    @37
    eqid
    brab2a
    a1i
    wph
    @51
    @16
    @8
    wph
    @50
    @15
    vx
    cP
    wph
    @43
    @11
    @49
    @14
    wph
    @42
    @1
    @9
    @10
    wph
    @39
    @40
    @41
    cF
    cD
    cE
    wph
    cD
    cP
    wcel
    @39
    cD
    wceq
    isleag.d
    cD
    cE
    cF
    cP
    s3fv0
    syl
    #
    wph
    cE
    cP
    wcel
    @40
    cE
    wceq
    isleag.e
    cD
    cE
    cF
    cP
    s3fv1
    syl
    #
    wph
    cF
    cP
    wcel
    @41
    cF
    wceq
    isleag.f
    cD
    cE
    cF
    cP
    s3fv2
    syl
    s3eqd
    breq2d
    wph
    @47
    @0
    @48
    @12
    @13
    wph
    @44
    @45
    @46
    cC
    cA
    cB
    wph
    cA
    cP
    wcel
    @44
    cA
    wceq
    isleag.a
    cA
    cB
    cC
    cP
    s3fv0
    syl
    wph
    cB
    cP
    wcel
    @45
    cB
    wceq
    isleag.b
    cA
    cB
    cC
    cP
    s3fv1
    syl
    wph
    cC
    cP
    wcel
    @46
    cC
    wceq
    isleag.c
    cA
    cB
    cC
    cP
    s3fv2
    syl
    s3eqd
    wph
    @39
    @40
    @9
    @9
    cD
    cE
    @80
    @81
    wph
    @9
    eqidd
    s3eqd
    breq12d
    anbi12d
    rexbidv
    anbi2d
    3bitrd
    wph
    @8
    @16
    wph
    @6
    @7
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
    @6
    wph
    @83
    @84
    wph
    cA
    cB
    cC
    cP
    isleag.a
    isleag.b
    isleag.c
    s3cld
    @84
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
    @85
    @6
    wb
    cP
    @67
    cvv
    isleag.p
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
    @82
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
    @7
    wph
    @89
    @90
    wph
    cD
    cE
    cF
    cP
    isleag.d
    isleag.e
    isleag.f
    s3cld
    @90
    wph
    cD
    cE
    cF
    s3len
    a1i
    jca
    @86
    @87
    @91
    @7
    wb
    @88
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
    bitr4d
end
