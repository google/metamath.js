include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wo.mm"
include "w3a.mm"
include "copab.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wceq.mm"
include "simpl.mm"
include "neeq1d.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "orbi12d.mm"
include "3anbi123d.mm"
include "eqid.mm"
include "brab2a.mm"
include "a1i.mm"
include "cvv.mm"
include "chlg.mm"
include "cmpt.mm"
include "elex.mm"
include "cbs.mm"
include "citv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "3anbi3d.mm"
include "opabbidv.mm"
include "mpteq12dv.mm"
include "df-hlg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "syl5eq.mm"
include "neeq2.mm"
include "oveq1.mm"
include "anbi2d.mm"
include "adantl.mm"
include "cxp.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmptd.mm"
include "breqd.mm"
include "jca.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem ishlg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume ishlg.g: |- ( ph -> G e. V )


  assert |- ( ph -> ( A ( K ` C ) B <-> ( A =/= C /\ B =/= C /\ ( A e. ( C I B ) \/ B e. ( C I A ) ) ) ) )

  proof
    wph
    cA
    cB
    va
    cv
    #
    cP
    wcel
    #
    vb
    cv
    #
    cP
    wcel
    #
    wa
    #
    @0
    cC
    wne
    #
    @2
    cC
    wne
    #
    @0
    cC
    @2
    cI
    co
    #
    wcel
    #
    @2
    cC
    @0
    cI
    co
    #
    wcel
    #
    wo
    #
    w3a
    #
    wa
    #
    va
    vb
    copab
    #
    wbr
    #
    cA
    cP
    wcel
    #
    cB
    cP
    wcel
    #
    wa
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    cA
    cC
    cB
    cI
    co
    #
    wcel
    #
    cB
    cC
    cA
    cI
    co
    #
    wcel
    #
    wo
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cK
    cfv
    #
    wbr
    @26
    @15
    @27
    wb
    wph
    @12
    @26
    va
    vb
    cA
    cB
    cP
    cP
    @14
    @0
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    #
    @5
    @19
    @6
    @20
    @11
    @25
    @31
    @0
    cA
    cC
    @29
    @30
    simpl
    #
    neeq1d
    @31
    @2
    cB
    cC
    @29
    @30
    simpr
    #
    neeq1d
    @31
    @8
    @22
    @10
    @24
    @31
    @0
    cA
    @7
    @21
    @32
    @31
    @2
    cB
    cC
    cI
    @33
    oveq2d
    eleq12d
    @31
    @2
    cB
    @9
    @23
    @33
    @31
    @0
    cA
    cC
    cI
    @32
    oveq2d
    eleq12d
    orbi12d
    3anbi123d
    @14
    eqid
    brab2a
    a1i
    wph
    @28
    @14
    cA
    cB
    wph
    vc
    cC
    @4
    @0
    vc
    cv
    #
    wne
    #
    @2
    @34
    wne
    #
    @0
    @34
    @2
    cI
    co
    #
    wcel
    #
    @2
    @34
    @0
    cI
    co
    #
    wcel
    #
    wo
    #
    w3a
    #
    wa
    #
    va
    vb
    copab
    #
    @14
    cP
    cK
    cvv
    wph
    cK
    cG
    chlg
    cfv
    #
    vc
    cP
    @44
    cmpt
    #
    ishlg.k
    wph
    cG
    cV
    wcel
    cG
    cvv
    wcel
    @45
    @46
    wceq
    ishlg.g
    cG
    cV
    elex
    vg
    cG
    vc
    vg
    cv
    #
    cbs
    cfv
    #
    @0
    @48
    wcel
    #
    @2
    @48
    wcel
    #
    wa
    #
    @35
    @36
    @0
    @34
    @2
    @47
    citv
    cfv
    #
    co
    #
    wcel
    #
    @2
    @34
    @0
    @52
    co
    #
    wcel
    #
    wo
    #
    w3a
    #
    wa
    #
    va
    vb
    copab
    #
    cmpt
    @46
    cvv
    chlg
    @47
    cG
    wceq
    #
    vc
    @48
    @60
    cP
    @44
    @61
    @48
    cG
    cbs
    cfv
    #
    cP
    @47
    cG
    cbs
    fveq2
    ishlg.p
    syl6eqr
    #
    @61
    @59
    @43
    va
    vb
    @61
    @51
    @4
    @58
    @42
    @61
    @49
    @1
    @50
    @3
    @61
    @48
    cP
    @0
    @63
    eleq2d
    @61
    @48
    cP
    @2
    @63
    eleq2d
    anbi12d
    @61
    @57
    @41
    @35
    @36
    @61
    @54
    @38
    @56
    @40
    @61
    @53
    @37
    @0
    @61
    @52
    cI
    @34
    @2
    @61
    @52
    cG
    citv
    cfv
    cI
    @47
    cG
    citv
    fveq2
    ishlg.i
    syl6eqr
    #
    oveqd
    eleq2d
    @61
    @55
    @39
    @2
    @61
    @52
    cI
    @34
    @0
    @64
    oveqd
    eleq2d
    orbi12d
    3anbi3d
    anbi12d
    opabbidv
    mpteq12dv
    vg
    va
    vb
    vc
    df-hlg
    vc
    cP
    @44
    cP
    @62
    cvv
    ishlg.p
    cG
    cbs
    fvex
    eqeltri
    #
    mptex
    fvmpt
    3syl
    syl5eq
    @34
    cC
    wceq
    #
    @44
    @14
    wceq
    wph
    @66
    @43
    @13
    va
    vb
    @66
    @42
    @12
    @4
    @66
    @35
    @5
    @36
    @6
    @41
    @11
    @34
    cC
    @0
    neeq2
    @34
    cC
    @2
    neeq2
    @66
    @38
    @8
    @40
    @10
    @66
    @37
    @7
    @0
    @34
    cC
    @2
    cI
    oveq1
    eleq2d
    @66
    @39
    @9
    @2
    @34
    cC
    @0
    cI
    oveq1
    eleq2d
    orbi12d
    3anbi123d
    anbi2d
    opabbidv
    adantl
    ishlg.c
    @14
    cvv
    wcel
    wph
    @14
    cP
    cP
    cxp
    cP
    cP
    @65
    @65
    xpex
    @12
    va
    vb
    cP
    cP
    opabssxp
    ssexi
    a1i
    fvmptd
    breqd
    wph
    @18
    @26
    wph
    @16
    @17
    ishlg.a
    ishlg.b
    jca
    biantrurd
    3bitr4d
end
