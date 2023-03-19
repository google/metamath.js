include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cmid.mm"
include "co.mm"
include "wcel.mm"
include "cperpg.mm"
include "wbr.mm"
include "wo.mm"
include "wa.mm"
include "crio.mm"
include "clmi.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "clng.mm"
include "cbs.mm"
include "df-lmi.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "oveqd.mm"
include "eleq1d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "orbi1d.mm"
include "anbi12d.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "cstrkg.mm"
include "elex.mm"
include "syl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnexg.mm"
include "mptexg.mm"
include "mp2b.mm"
include "fvmptd.mm"
include "eleq2.mm"
include "breq1.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "mptex.mm"
include "syl5eq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "wreu.mm"
include "lmieu.mm"
include "riotacl.mm"
include "eqeq2d.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "riota2.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem islmib
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )
  assume lmicl.1: |- ( ph -> A e. P )
  assume islmib.b: |- ( ph -> B e. P )


  assert |- ( ph -> ( B = ( M ` A ) <-> ( ( A ( midG ` G ) B ) e. D /\ ( D ( perpG ` G ) ( A L B ) \/ A = B ) ) ) )

  proof
    wph
    cB
    cA
    cM
    cfv
    #
    wceq
    cB
    cA
    vb
    cv
    #
    cG
    cmid
    cfv
    #
    co
    #
    cD
    wcel
    #
    cD
    cA
    @1
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    cA
    @1
    wceq
    #
    wo
    #
    wa
    #
    vb
    cP
    crio
    #
    wceq
    #
    cA
    cB
    @2
    co
    #
    cD
    wcel
    #
    cD
    cA
    cB
    cL
    co
    #
    @6
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    wa
    #
    wph
    @0
    @11
    cB
    wph
    va
    cA
    va
    cv
    #
    @1
    @2
    co
    #
    cD
    wcel
    #
    cD
    @20
    @1
    cL
    co
    #
    @6
    wbr
    #
    @20
    @1
    wceq
    #
    wo
    #
    wa
    #
    vb
    cP
    crio
    #
    @11
    cP
    cM
    cP
    wph
    cM
    cD
    cG
    clmi
    cfv
    #
    cfv
    va
    cP
    @28
    cmpt
    #
    lmif.m
    wph
    vd
    cD
    va
    cP
    @21
    vd
    cv
    #
    wcel
    #
    @31
    @23
    @6
    wbr
    #
    @25
    wo
    #
    wa
    #
    vb
    cP
    crio
    #
    cmpt
    #
    @30
    cL
    crn
    #
    @29
    cvv
    wph
    vg
    cG
    vd
    vg
    cv
    #
    clng
    cfv
    #
    crn
    #
    va
    @39
    cbs
    cfv
    #
    @20
    @1
    @39
    cmid
    cfv
    #
    co
    #
    @31
    wcel
    #
    @31
    @20
    @1
    @40
    co
    #
    @39
    cperpg
    cfv
    #
    wbr
    #
    @25
    wo
    #
    wa
    #
    vb
    @42
    crio
    #
    cmpt
    #
    cmpt
    #
    vd
    @38
    @37
    cmpt
    #
    cvv
    clmi
    cvv
    clmi
    vg
    cvv
    @53
    cmpt
    wceq
    wph
    vg
    vd
    va
    vb
    df-lmi
    a1i
    @39
    cG
    wceq
    #
    @53
    @54
    wceq
    wph
    @55
    vd
    @41
    @52
    @38
    @37
    @55
    @40
    cL
    @55
    @40
    cG
    clng
    cfv
    #
    cL
    @39
    cG
    clng
    fveq2
    lmif.l
    syl6eqr
    #
    rneqd
    @55
    va
    @42
    @51
    cP
    @36
    @55
    @42
    cG
    cbs
    cfv
    #
    cP
    @39
    cG
    cbs
    fveq2
    ismid.p
    syl6eqr
    #
    @55
    @50
    @35
    vb
    @42
    cP
    @59
    @55
    @45
    @32
    @49
    @34
    @55
    @44
    @21
    @31
    @55
    @43
    @2
    @20
    @1
    @39
    cG
    cmid
    fveq2
    oveqd
    eleq1d
    @55
    @48
    @33
    @25
    @55
    @31
    @31
    @46
    @23
    @47
    @6
    @55
    @31
    eqidd
    @39
    cG
    cperpg
    fveq2
    @55
    @40
    cL
    @20
    @1
    @57
    oveqd
    breq123d
    orbi1d
    anbi12d
    riotaeqbidv
    mpteq12dv
    mpteq12dv
    adantl
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    ismid.g
    cG
    cstrkg
    elex
    syl
    @54
    cvv
    wcel
    #
    wph
    cL
    cvv
    wcel
    @38
    cvv
    wcel
    @60
    cL
    @56
    cvv
    lmif.l
    cG
    clng
    fvex
    eqeltri
    cL
    cvv
    rnexg
    vd
    @38
    @37
    cvv
    mptexg
    mp2b
    a1i
    fvmptd
    @31
    cD
    wceq
    #
    @37
    @30
    wceq
    wph
    @61
    va
    cP
    @36
    @28
    @61
    @35
    @27
    vb
    cP
    @61
    @32
    @22
    @34
    @26
    @31
    cD
    @21
    eleq2
    @61
    @33
    @24
    @25
    @31
    cD
    @23
    @6
    breq1
    orbi1d
    anbi12d
    riotabidv
    mpteq2dv
    adantl
    lmif.d
    @30
    cvv
    wcel
    wph
    va
    cP
    @28
    cP
    @58
    cvv
    ismid.p
    cG
    cbs
    fvex
    eqeltri
    mptex
    a1i
    fvmptd
    syl5eq
    @20
    cA
    wceq
    #
    @28
    @11
    wceq
    wph
    @62
    @27
    @10
    vb
    cP
    @62
    @22
    @4
    @26
    @9
    @62
    @21
    @3
    cD
    @20
    cA
    @1
    @2
    oveq1
    eleq1d
    @62
    @24
    @7
    @25
    @8
    @62
    @23
    @5
    cD
    @6
    @20
    cA
    @1
    cL
    oveq1
    breq2d
    @20
    cA
    @1
    eqeq1
    orbi12d
    anbi12d
    riotabidv
    adantl
    lmicl.1
    wph
    @10
    vb
    cP
    wreu
    #
    @11
    cP
    wcel
    wph
    cA
    cD
    cP
    cG
    cI
    cL
    c.mi
    vb
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.l
    lmif.d
    lmicl.1
    lmieu
    #
    @10
    vb
    cP
    riotacl
    syl
    fvmptd
    eqeq2d
    wph
    @19
    @11
    cB
    wceq
    #
    @12
    wph
    cB
    cP
    wcel
    @63
    @19
    @65
    wb
    islmib.b
    @64
    @10
    @19
    vb
    cP
    cB
    @1
    cB
    wceq
    #
    @4
    @14
    @9
    @18
    @66
    @3
    @13
    cD
    @1
    cB
    cA
    @2
    oveq2
    eleq1d
    @66
    @7
    @16
    @8
    @17
    @66
    @5
    @15
    cD
    @6
    @1
    cB
    cA
    cL
    oveq2
    breq2d
    @1
    cB
    cA
    eqeq2
    orbi12d
    anbi12d
    riota2
    syl2anc
    cB
    @11
    eqcom
    syl6bbr
    bitr4d
end
