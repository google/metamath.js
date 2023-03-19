include "cs3.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "wne.mm"
include "c2.mm"
include "w3a.mm"
include "wceq.mm"
include "wbr.mm"
include "wo.mm"
include "wrex.mm"
include "copab.mm"
include "cinag.mm"
include "wb.mm"
include "simpr.mm"
include "fveq1d.mm"
include "neeq12d.mm"
include "simpl.mm"
include "3anbi123d.mm"
include "eqidd.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "eqeq12d.mm"
include "fveq2d.mm"
include "breq123d.mm"
include "orbi12d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "eqid.mm"
include "brab2a.mm"
include "a1i.mm"
include "biidd.mm"
include "s3fv0.mm"
include "syl.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "neeq2d.mm"
include "eleq2d.mm"
include "eqeq2d.mm"
include "breqd.mm"
include "bitrd.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "citv.mm"
include "chlg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "oveqd.mm"
include "orbi2d.mm"
include "rexeqbidv.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "df-inag.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
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
include "3nn0.mm"
include "wrdmap.mm"
include "mp2an.mm"
include "sylib.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem isinag
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  let vp: setvar p
  let vt: setvar t
  let vg: setvar g
  assume isinag.p: |- P = ( Base ` G )
  assume isinag.i: |- I = ( Itv ` G )
  assume isinag.k: |- K = ( hlG ` G )
  assume isinag.x: |- ( ph -> X e. P )
  assume isinag.a: |- ( ph -> A e. P )
  assume isinag.b: |- ( ph -> B e. P )
  assume isinag.c: |- ( ph -> C e. P )
  assume isinag.g: |- ( ph -> G e. V )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint G x
  disjoint P x
  disjoint X x
  disjoint ph x
  disjoint A p
  disjoint A t
  disjoint p t
  disjoint p x
  disjoint t x
  disjoint B p
  disjoint B t
  disjoint C p
  disjoint C t
  disjoint G g
  disjoint G p
  disjoint G t
  disjoint g p
  disjoint g t
  disjoint g x
  disjoint I g
  disjoint I p
  disjoint I t
  disjoint K g
  disjoint K p
  disjoint K t
  disjoint P g
  disjoint P p
  disjoint P t
  disjoint X p
  disjoint X t
  assert |- ( ph -> ( X ( inA ` G ) <" A B C "> <-> ( ( A =/= B /\ C =/= B /\ X =/= B ) /\ E. x e. P ( x e. ( A I C ) /\ ( x = B \/ x ( K ` B ) X ) ) ) ) )

  proof
    wph
    cX
    cA
    cB
    cC
    cs3
    #
    vp
    cv
    #
    cP
    wcel
    #
    vt
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
    wa
    #
    cc0
    @3
    cfv
    #
    c1
    @3
    cfv
    #
    wne
    #
    c2
    @3
    cfv
    #
    @9
    wne
    #
    @1
    @9
    wne
    #
    w3a
    #
    vx
    cv
    #
    @8
    @11
    cI
    co
    #
    wcel
    #
    @15
    @9
    wceq
    #
    @15
    @1
    @9
    cK
    cfv
    #
    wbr
    #
    wo
    #
    wa
    #
    vx
    cP
    wrex
    #
    wa
    #
    wa
    #
    vp
    vt
    copab
    #
    wbr
    #
    cX
    cP
    wcel
    #
    @0
    @5
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    cC
    cB
    wne
    #
    cX
    cB
    wne
    #
    w3a
    #
    @15
    cA
    cC
    cI
    co
    #
    wcel
    #
    @15
    cB
    wceq
    #
    @15
    cX
    cB
    cK
    cfv
    #
    wbr
    #
    wo
    #
    wa
    #
    vx
    cP
    wrex
    #
    wa
    #
    wa
    #
    cX
    @0
    cG
    cinag
    cfv
    #
    wbr
    @43
    wph
    @27
    @30
    cc0
    @0
    cfv
    #
    c1
    @0
    cfv
    #
    wne
    #
    c2
    @0
    cfv
    #
    @47
    wne
    #
    cX
    @47
    wne
    #
    w3a
    #
    @15
    @46
    @49
    cI
    co
    #
    wcel
    #
    @15
    @47
    wceq
    #
    @15
    cX
    @47
    cK
    cfv
    #
    wbr
    #
    wo
    #
    wa
    #
    vx
    cP
    wrex
    #
    wa
    #
    wa
    #
    @44
    @27
    @62
    wb
    wph
    @24
    @61
    vp
    vt
    cX
    @0
    cP
    @5
    @26
    @1
    cX
    wceq
    #
    @3
    @0
    wceq
    #
    wa
    #
    @14
    @52
    @23
    @60
    @65
    @10
    @48
    @12
    @50
    @13
    @51
    @65
    @8
    @46
    @9
    @47
    @65
    cc0
    @3
    @0
    @63
    @64
    simpr
    #
    fveq1d
    #
    @65
    c1
    @3
    @0
    @66
    fveq1d
    #
    neeq12d
    @65
    @11
    @49
    @9
    @47
    @65
    c2
    @3
    @0
    @66
    fveq1d
    #
    @68
    neeq12d
    @65
    @1
    cX
    @9
    @47
    @63
    @64
    simpl
    #
    @68
    neeq12d
    3anbi123d
    @65
    @22
    @59
    vx
    cP
    @65
    @17
    @54
    @21
    @58
    @65
    @15
    @15
    @16
    @53
    @65
    @15
    eqidd
    #
    @65
    @8
    @46
    @11
    @49
    cI
    @67
    @69
    oveq12d
    eleq12d
    @65
    @18
    @55
    @20
    @57
    @65
    @15
    @15
    @9
    @47
    @71
    @68
    eqeq12d
    @65
    @15
    @15
    @1
    cX
    @19
    @56
    @71
    @65
    @9
    @47
    cK
    @68
    fveq2d
    @70
    breq123d
    orbi12d
    anbi12d
    rexbidv
    anbi12d
    @26
    eqid
    brab2a
    a1i
    wph
    @30
    @30
    @61
    @43
    wph
    @30
    biidd
    wph
    @52
    @34
    @60
    @42
    wph
    @48
    @31
    @50
    @32
    @51
    @33
    wph
    @46
    cA
    @47
    cB
    wph
    cA
    cP
    wcel
    @46
    cA
    wceq
    isinag.a
    cA
    cB
    cC
    cP
    s3fv0
    syl
    #
    wph
    cB
    cP
    wcel
    @47
    cB
    wceq
    isinag.b
    cA
    cB
    cC
    cP
    s3fv1
    syl
    #
    neeq12d
    wph
    @49
    cC
    @47
    cB
    wph
    cC
    cP
    wcel
    @49
    cC
    wceq
    isinag.c
    cA
    cB
    cC
    cP
    s3fv2
    syl
    #
    @73
    neeq12d
    wph
    @47
    cB
    cX
    @73
    neeq2d
    3anbi123d
    wph
    @59
    @41
    vx
    cP
    wph
    @54
    @36
    @58
    @40
    wph
    @53
    @35
    @15
    wph
    @46
    cA
    @49
    cC
    cI
    @72
    @74
    oveq12d
    eleq2d
    wph
    @55
    @37
    @57
    @39
    wph
    @47
    cB
    @15
    @73
    eqeq2d
    wph
    @56
    @38
    @15
    cX
    wph
    @47
    cB
    cK
    @73
    fveq2d
    breqd
    orbi12d
    anbi12d
    rexbidv
    anbi12d
    anbi12d
    bitrd
    wph
    @45
    @26
    cX
    @0
    wph
    cG
    cV
    wcel
    cG
    cvv
    wcel
    @45
    @26
    wceq
    isinag.g
    cG
    cV
    elex
    vg
    cG
    @1
    vg
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    @76
    @4
    cmap
    co
    #
    wcel
    #
    wa
    #
    @14
    @15
    @8
    @11
    @75
    citv
    cfv
    #
    co
    #
    wcel
    #
    @18
    @15
    @1
    @9
    @75
    chlg
    cfv
    #
    cfv
    #
    wbr
    #
    wo
    #
    wa
    #
    vx
    @76
    wrex
    #
    wa
    #
    wa
    #
    vp
    vt
    copab
    @26
    cvv
    cinag
    @75
    cG
    wceq
    #
    @91
    @25
    vp
    vt
    @92
    @80
    @7
    @90
    @24
    @92
    @77
    @2
    @79
    @6
    @92
    @76
    cP
    @1
    @92
    @76
    cG
    cbs
    cfv
    #
    cP
    @75
    cG
    cbs
    fveq2
    isinag.p
    syl6eqr
    #
    eleq2d
    @92
    @78
    @5
    @3
    @92
    @76
    cP
    @4
    cmap
    @94
    oveq1d
    eleq2d
    anbi12d
    @92
    @89
    @23
    @14
    @92
    @88
    @22
    vx
    @76
    cP
    @94
    @92
    @83
    @17
    @87
    @21
    @92
    @82
    @16
    @15
    @92
    @81
    cI
    @8
    @11
    @92
    @81
    cG
    citv
    cfv
    cI
    @75
    cG
    citv
    fveq2
    isinag.i
    syl6eqr
    oveqd
    eleq2d
    @92
    @86
    @20
    @18
    @92
    @85
    @19
    @15
    @1
    @92
    @9
    @84
    cK
    @92
    @84
    cG
    chlg
    cfv
    cK
    @75
    cG
    chlg
    fveq2
    isinag.k
    syl6eqr
    fveq1d
    breqd
    orbi2d
    anbi12d
    rexeqbidv
    anbi2d
    anbi12d
    opabbidv
    vx
    vt
    vg
    vp
    df-inag
    @26
    cP
    @5
    cxp
    cP
    @5
    cP
    @93
    cvv
    isinag.p
    cG
    cbs
    fvex
    eqeltri
    #
    cP
    @4
    cmap
    ovex
    xpex
    @24
    vp
    vt
    cP
    @5
    opabssxp
    ssexi
    fvmpt
    3syl
    breqd
    wph
    @30
    @43
    wph
    @28
    @29
    isinag.x
    wph
    @0
    cP
    cword
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
    @29
    wph
    @96
    @97
    wph
    cA
    cB
    cC
    cP
    isinag.a
    isinag.b
    isinag.c
    s3cld
    @97
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
    c3
    cn0
    wcel
    @98
    @29
    wb
    @95
    3nn0
    c3
    cP
    @0
    cvv
    wrdmap
    mp2an
    sylib
    jca
    biantrurd
    3bitr4d
end
