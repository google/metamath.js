include "cfv.mm"
include "ccom.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "crest.mm"
include "ccnp.mm"
include "wa.mm"
include "cuni.mm"
include "eqid.mm"
include "cnprcl.mm"
include "syl.mm"
include "ctopon.mm"
include "cc.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "toponuni.mm"
include "eleqtrrd.mm"
include "ad2antrr.mm"
include "wn.mm"
include "wf.mm"
include "wo.mm"
include "elun.mm"
include "elsni.mm"
include "orim2i.mm"
include "sylbi.mm"
include "adantl.mm"
include "orcomd.mm"
include "orcanai.mm"
include "ffvelrnd.mm"
include "ifclda.mm"
include "eqidd.mm"
include "a1i.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "ifeq2da.mm"
include "fvif.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "fssd.mm"
include "cdm.mm"
include "fdm.mm"
include "w3a.mm"
include "limcrcl.mm"
include "simp2d.mm"
include "eqsstr3d.mm"
include "simp3d.mm"
include "ellimc.mm"
include "mpbid.mm"
include "ctop.mm"
include "wb.mm"
include "cnfldtop.mm"
include "fmptd.mm"
include "snssd.mm"
include "unssd.mm"
include "feq2d.mm"
include "toponunii.mm"
include "cnprest2.mm"
include "oveq2i.mm"
include "fveq1i.mm"
include "syl6eleqr.mm"
include "ssun2.mm"
include "snssg.mm"
include "mpbiri.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "fveq2d.mm"
include "cnpco.mm"
include "eqeltrrd.mm"
include "fco.mm"
include "mpbird.mm"

theorem limccnp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume limccnp.f: |- ( ph -> F : A --> D )
  assume limccnp.d: |- ( ph -> D C_ CC )
  assume limccnp.k: |- K = ( TopOpen ` CCfld )
  assume limccnp.j: |- J = ( K |`t D )
  assume limccnp.c: |- ( ph -> C e. ( F limCC B ) )
  assume limccnp.b: |- ( ph -> G e. ( ( J CnP K ) ` C ) )


  assert |- ( ph -> ( G ` C ) e. ( ( G o. F ) limCC B ) )

  proof
    wph
    cC
    cG
    cfv
    #
    cG
    cF
    ccom
    #
    cB
    climc
    co
    wcel
    vx
    cA
    cB
    csn
    #
    cun
    #
    vx
    cv
    #
    cB
    wceq
    #
    @0
    @4
    @1
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cK
    @3
    crest
    co
    #
    cK
    ccnp
    co
    cfv
    #
    wcel
    wph
    cG
    vx
    @3
    @5
    cC
    @4
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    ccom
    #
    @8
    @10
    wph
    @14
    vx
    @3
    @12
    cG
    cfv
    #
    cmpt
    @8
    wph
    vx
    vy
    @3
    cD
    @12
    vy
    cv
    #
    cG
    cfv
    @15
    @13
    cG
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @5
    cC
    @11
    cD
    wph
    cC
    cD
    wcel
    #
    @17
    @5
    wph
    cC
    cJ
    cuni
    #
    cD
    wph
    cG
    cC
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    cC
    @20
    wcel
    limccnp.b
    cC
    cG
    cJ
    cK
    @20
    @20
    eqid
    cnprcl
    syl
    wph
    cJ
    cD
    ctopon
    cfv
    #
    wcel
    #
    cD
    @20
    wceq
    wph
    cJ
    cK
    cD
    crest
    co
    #
    @24
    limccnp.j
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    #
    cD
    cc
    wss
    #
    @26
    @24
    wcel
    cK
    limccnp.k
    cnfldtopon
    #
    limccnp.d
    cD
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    #
    cD
    cJ
    toponuni
    syl
    eleqtrrd
    #
    ad2antrr
    @18
    @5
    wn
    #
    wa
    #
    cA
    cD
    @4
    cF
    wph
    cA
    cD
    cF
    wf
    #
    @17
    @32
    limccnp.f
    ad2antrr
    #
    @18
    @5
    @4
    cA
    wcel
    #
    @18
    @36
    @5
    @17
    @36
    @5
    wo
    #
    wph
    @17
    @36
    @4
    @2
    wcel
    #
    wo
    @37
    @4
    cA
    @2
    elun
    @38
    @5
    @36
    @4
    cB
    elsni
    orim2i
    sylbi
    adantl
    orcomd
    orcanai
    #
    ffvelrnd
    ifclda
    #
    wph
    @13
    eqidd
    wph
    vy
    cD
    cc
    cG
    wph
    @25
    @27
    @23
    cD
    cc
    cG
    wf
    #
    @30
    @27
    wph
    @29
    a1i
    limccnp.b
    cC
    cG
    cJ
    cK
    cD
    cc
    cnpf2
    syl3anc
    #
    feqmptd
    @16
    @12
    cG
    fveq2
    fmptco
    wph
    vx
    @3
    @7
    @15
    @18
    @7
    @5
    @0
    @11
    cG
    cfv
    #
    cif
    @15
    @18
    @5
    @6
    @43
    @0
    @33
    @34
    @36
    @6
    @43
    wceq
    @35
    @39
    cA
    cD
    @4
    cG
    cF
    fvco3
    syl2anc
    ifeq2da
    @5
    cC
    @11
    cG
    fvif
    syl6eqr
    mpteq2dva
    eqtr4d
    wph
    @13
    cB
    @9
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    cG
    cB
    @13
    cfv
    #
    @21
    cfv
    #
    wcel
    @14
    @10
    wcel
    wph
    @13
    cB
    @9
    @26
    ccnp
    co
    #
    cfv
    #
    @45
    wph
    @13
    @10
    wcel
    #
    @13
    @49
    wcel
    #
    wph
    cC
    cF
    cB
    climc
    co
    wcel
    #
    @50
    limccnp.c
    wph
    vx
    cA
    cB
    cC
    cF
    @13
    @9
    cK
    @9
    eqid
    #
    limccnp.k
    @13
    eqid
    #
    wph
    cA
    cD
    cc
    cF
    limccnp.f
    limccnp.d
    fssd
    wph
    cA
    cF
    cdm
    #
    cc
    wph
    @34
    @55
    cA
    wceq
    limccnp.f
    cA
    cD
    cF
    fdm
    syl
    wph
    @55
    cc
    cF
    wf
    #
    @55
    cc
    wss
    #
    cB
    cc
    wcel
    #
    wph
    @52
    @56
    @57
    @58
    w3a
    limccnp.c
    cB
    cC
    cF
    limcrcl
    syl
    #
    simp2d
    eqsstr3d
    #
    wph
    @56
    @57
    @58
    @59
    simp3d
    #
    ellimc
    mpbid
    wph
    cK
    ctop
    wcel
    #
    @9
    cuni
    #
    cD
    @13
    wf
    #
    @28
    @50
    @51
    wb
    @62
    wph
    cK
    limccnp.k
    cnfldtop
    a1i
    wph
    @3
    cD
    @13
    wf
    @64
    wph
    vx
    @3
    @12
    cD
    @13
    @40
    @54
    fmptd
    wph
    @3
    @63
    cD
    @13
    wph
    @9
    @3
    ctopon
    cfv
    wcel
    #
    @3
    @63
    wceq
    wph
    @27
    @3
    cc
    wss
    @65
    @29
    wph
    cA
    @2
    cc
    @60
    wph
    cB
    cc
    @61
    snssd
    unssd
    @3
    cK
    cc
    resttopon
    sylancr
    @3
    @9
    toponuni
    syl
    feq2d
    mpbid
    limccnp.d
    cD
    cB
    @13
    @9
    cK
    @63
    cc
    @63
    eqid
    cc
    cK
    @29
    toponunii
    cnprest2
    syl3anc
    mpbid
    cB
    @44
    @48
    cJ
    @26
    @9
    ccnp
    limccnp.j
    oveq2i
    fveq1i
    syl6eleqr
    wph
    cG
    @22
    @47
    limccnp.b
    wph
    @46
    cC
    @21
    wph
    cB
    @3
    wcel
    #
    @19
    @46
    cC
    wceq
    wph
    @66
    @2
    @3
    wss
    #
    @2
    cA
    ssun2
    wph
    @58
    @66
    @67
    wb
    @61
    cB
    @3
    cc
    snssg
    syl
    mpbiri
    @31
    vx
    cB
    @12
    cC
    @3
    cD
    @13
    @5
    cC
    @11
    iftrue
    @54
    fvmptg
    syl2anc
    fveq2d
    eleqtrrd
    cB
    @13
    cG
    @9
    cJ
    cK
    cnpco
    syl2anc
    eqeltrrd
    wph
    vx
    cA
    cB
    @0
    @1
    @8
    @9
    cK
    @53
    limccnp.k
    @8
    eqid
    wph
    @41
    @34
    cA
    cc
    @1
    wf
    @42
    limccnp.f
    cA
    cD
    cc
    cG
    cF
    fco
    syl2anc
    @60
    @61
    ellimc
    mpbird
end
