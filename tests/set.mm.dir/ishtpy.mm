include "chtpy.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "crab.mm"
include "cvv.mm"
include "ctop.mm"
include "cuni.mm"
include "cmpt2.mm"
include "df-htpy.mm"
include "a1i.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "unieqd.mm"
include "ctopon.mm"
include "toponuni.mm"
include "syl.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "raleqdv.mm"
include "rabeqbidv.mm"
include "mpt2eq123dv.mm"
include "topontop.mm"
include "cntop2.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "ovex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "xpex.mm"
include "pwex.mm"
include "fex2.mm"
include "mp3an.mm"
include "ovmpt2d.mm"
include "wb.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "bi2anan9.mm"
include "adantl.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "rabex.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem ishtpy
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ishtpy.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume ishtpy.3: |- ( ph -> F e. ( J Cn K ) )
  assume ishtpy.4: |- ( ph -> G e. ( J Cn K ) )

  disjoint F s
  disjoint G s
  disjoint H s
  disjoint J s
  disjoint ph s
  disjoint X s
  disjoint A s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint F g
  disjoint h s
  disjoint h t
  disjoint F h
  disjoint s t
  disjoint F t
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G t
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint H x
  disjoint H y
  disjoint M t
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint g j
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint h j
  disjoint h k
  disjoint h z
  disjoint J h
  disjoint j k
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint J k
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint x z
  disjoint J x
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint K j
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X j
  disjoint X k
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( H e. ( F ( J Htpy K ) G ) <-> ( H e. ( ( J tX II ) Cn K ) /\ A. s e. X ( ( s H 0 ) = ( F ` s ) /\ ( s H 1 ) = ( G ` s ) ) ) ) )

  proof
    wph
    cH
    cF
    cG
    cJ
    cK
    chtpy
    co
    #
    co
    #
    wcel
    cH
    vs
    cv
    #
    cc0
    vh
    cv
    #
    co
    #
    @2
    cF
    cfv
    #
    wceq
    #
    @2
    c1
    @3
    co
    #
    @2
    cG
    cfv
    #
    wceq
    #
    wa
    #
    vs
    cX
    wral
    #
    vh
    cJ
    cii
    ctx
    co
    #
    cK
    ccn
    co
    #
    crab
    #
    wcel
    cH
    @13
    wcel
    @2
    cc0
    cH
    co
    #
    @5
    wceq
    #
    @2
    c1
    cH
    co
    #
    @8
    wceq
    #
    wa
    #
    vs
    cX
    wral
    #
    wa
    wph
    @1
    @14
    cH
    wph
    vf
    vg
    cF
    cG
    cJ
    cK
    ccn
    co
    #
    @21
    @4
    @2
    vf
    cv
    #
    cfv
    #
    wceq
    #
    @7
    @2
    vg
    cv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vs
    cX
    wral
    #
    vh
    @13
    crab
    #
    @14
    @0
    cvv
    wph
    vj
    vk
    cJ
    cK
    ctop
    ctop
    vf
    vg
    vj
    cv
    #
    vk
    cv
    #
    ccn
    co
    #
    @33
    @28
    vs
    @31
    cuni
    #
    wral
    #
    vh
    @31
    cii
    ctx
    co
    #
    @32
    ccn
    co
    #
    crab
    #
    cmpt2
    #
    vf
    vg
    @21
    @21
    @30
    cmpt2
    #
    chtpy
    cvv
    chtpy
    vj
    vk
    ctop
    ctop
    @39
    cmpt2
    wceq
    wph
    vj
    vk
    vf
    vg
    vh
    vs
    df-htpy
    a1i
    wph
    @31
    cJ
    wceq
    #
    @32
    cK
    wceq
    #
    wa
    #
    wa
    #
    vf
    vg
    @33
    @33
    @38
    @21
    @21
    @30
    @44
    @31
    cJ
    @32
    cK
    ccn
    wph
    @41
    @42
    simprl
    #
    wph
    @41
    @42
    simprr
    #
    oveq12d
    #
    @47
    @44
    @35
    @29
    vh
    @37
    @13
    @44
    @36
    @12
    @32
    cK
    ccn
    @44
    @31
    cJ
    cii
    ctx
    @45
    oveq1d
    @46
    oveq12d
    @44
    @28
    vs
    @34
    cX
    @44
    @34
    cJ
    cuni
    #
    cX
    @44
    @31
    cJ
    @45
    unieqd
    wph
    cX
    @48
    wceq
    #
    @43
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @49
    ishtpy.1
    cX
    cJ
    toponuni
    syl
    adantr
    eqtr4d
    raleqdv
    rabeqbidv
    mpt2eq123dv
    wph
    @50
    cJ
    ctop
    wcel
    ishtpy.1
    cX
    cJ
    topontop
    syl
    wph
    cF
    @21
    wcel
    cK
    ctop
    wcel
    ishtpy.3
    cF
    cJ
    cK
    cntop2
    syl
    @40
    cvv
    wcel
    #
    wph
    @21
    @21
    cxp
    #
    @13
    cpw
    #
    @40
    wf
    #
    @52
    cvv
    wcel
    @53
    cvv
    wcel
    @51
    @30
    @53
    wcel
    #
    vg
    @21
    wral
    vf
    @21
    wral
    @54
    @55
    vf
    vg
    @21
    @21
    @55
    @30
    @13
    wss
    @29
    vh
    @13
    ssrab2
    @30
    @13
    @12
    cK
    ccn
    ovex
    #
    elpw2
    mpbir
    rgen2w
    vf
    vg
    @21
    @21
    @30
    @53
    @40
    @40
    eqid
    fmpt2
    mpbi
    @21
    @21
    cJ
    cK
    ccn
    ovex
    #
    @57
    xpex
    @13
    @56
    pwex
    @52
    @53
    @40
    cvv
    cvv
    fex2
    mp3an
    a1i
    ovmpt2d
    wph
    @22
    cF
    wceq
    #
    @25
    cG
    wceq
    #
    wa
    #
    wa
    #
    @29
    @11
    vh
    @13
    @61
    @28
    @10
    vs
    cX
    @60
    @28
    @10
    wb
    wph
    @58
    @24
    @6
    @59
    @27
    @9
    @58
    @23
    @5
    @4
    @2
    @22
    cF
    fveq1
    eqeq2d
    @59
    @26
    @8
    @7
    @2
    @25
    cG
    fveq1
    eqeq2d
    bi2anan9
    adantl
    ralbidv
    rabbidv
    ishtpy.3
    ishtpy.4
    @14
    cvv
    wcel
    wph
    @11
    vh
    @13
    @56
    rabex
    a1i
    ovmpt2d
    eleq2d
    @11
    @20
    vh
    cH
    @13
    @3
    cH
    wceq
    #
    @10
    @19
    vs
    cX
    @62
    @6
    @16
    @9
    @18
    @62
    @4
    @15
    @5
    @2
    cc0
    @3
    cH
    oveq
    eqeq1d
    @62
    @7
    @17
    @8
    @2
    c1
    @3
    cH
    oveq
    eqeq1d
    anbi12d
    ralbidv
    elrab
    syl6bb
end
