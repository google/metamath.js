include "cneg.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "limccl.mm"
include "sseldi.mm"
include "negcld.mm"
include "fmptd.mm"
include "limcmptdm.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "limcrcl.mm"
include "syl.mm"
include "simp3d.mm"
include "ellimc3.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "simplll.mm"
include "3ad2ant1.mm"
include "simp1r.mm"
include "simp3.mm"
include "simp2.mm"
include "mpd.mm"
include "wceq.mm"
include "nfv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfneg.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "negeqd.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "chvar.mm"
include "oveq1d.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "negsubdi3d.mm"
include "fveq2d.mm"
include "subcld.mm"
include "absnegd.mm"
include "eqtrd.mm"
include "eqbrtrd.mm"
include "syl21anc.mm"
include "3exp.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"

theorem neglimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume neglimc.f: |- F = ( x e. A |-> B )
  assume neglimc.g: |- G = ( x e. A |-> -u B )
  assume neglimc.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume neglimc.c: |- ( ph -> C e. ( F limCC D ) )

  disjoint A x
  disjoint ph x
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint v x
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint ph v
  disjoint ph w
  disjoint ph y
  assert |- ( ph -> -u C e. ( G limCC D ) )

  proof
    wph
    cC
    cneg
    #
    cG
    cD
    climc
    co
    wcel
    @0
    cc
    wcel
    vv
    cv
    #
    cD
    wne
    @1
    cD
    cmin
    co
    cabs
    cfv
    vw
    cv
    #
    clt
    wbr
    wa
    #
    @1
    cG
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    vw
    crp
    wrex
    #
    vy
    crp
    wral
    wph
    cC
    wph
    cF
    cD
    climc
    co
    #
    cc
    cC
    cD
    cF
    limccl
    neglimc.c
    sseldi
    #
    negcld
    wph
    @11
    vy
    crp
    wph
    @7
    crp
    wcel
    #
    wa
    #
    @3
    @1
    cF
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    vw
    crp
    wrex
    #
    @11
    wph
    @22
    vy
    crp
    wph
    cC
    cc
    wcel
    #
    @22
    vy
    crp
    wral
    #
    wph
    cC
    @12
    wcel
    #
    @23
    @24
    wa
    neglimc.c
    wph
    vy
    vw
    vv
    cA
    cD
    cC
    cF
    wph
    vx
    cA
    cB
    cc
    cF
    neglimc.b
    neglimc.f
    fmptd
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    neglimc.f
    neglimc.b
    neglimc.c
    limcmptdm
    #
    wph
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @28
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    @25
    @29
    @30
    @31
    w3a
    neglimc.c
    cD
    cC
    cF
    limcrcl
    syl
    simp3d
    #
    ellimc3
    mpbid
    simprd
    r19.21bi
    @15
    @21
    @10
    vw
    crp
    @15
    @2
    crp
    wcel
    #
    wa
    #
    @20
    @9
    vv
    cA
    @34
    @1
    cA
    wcel
    #
    wa
    #
    @20
    @3
    @8
    @36
    @20
    @3
    w3a
    #
    wph
    @35
    @19
    @8
    @36
    @20
    wph
    @3
    wph
    @14
    @33
    @35
    simplll
    3ad2ant1
    @34
    @35
    @20
    @3
    simp1r
    @37
    @3
    @19
    @36
    @20
    @3
    simp3
    @36
    @20
    @3
    simp2
    mpd
    wph
    @35
    wa
    #
    @19
    wa
    @6
    @18
    @7
    clt
    @38
    @6
    @18
    wceq
    @19
    @38
    @6
    @17
    cneg
    #
    cabs
    cfv
    @18
    @38
    @5
    @39
    cabs
    @38
    @5
    @16
    cneg
    #
    @0
    cmin
    co
    @39
    @38
    @4
    @40
    @0
    cmin
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @41
    cG
    cfv
    #
    @41
    cF
    cfv
    #
    cneg
    #
    wceq
    #
    wi
    @38
    @4
    @40
    wceq
    #
    wi
    vx
    vv
    @38
    @48
    vx
    @38
    vx
    nfv
    vx
    @4
    @40
    vx
    @1
    cG
    vx
    cG
    vx
    cA
    cB
    cneg
    #
    cmpt
    neglimc.g
    vx
    cA
    @49
    nfmpt1
    nfcxfr
    vx
    @1
    nfcv
    #
    nffv
    vx
    @16
    vx
    @1
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    neglimc.f
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    @50
    nffv
    nfneg
    nfeq
    nfim
    @41
    @1
    wceq
    #
    @43
    @38
    @47
    @48
    @51
    @42
    @35
    wph
    @41
    @1
    cA
    eleq1
    anbi2d
    @51
    @44
    @4
    @46
    @40
    @41
    @1
    cG
    fveq2
    @51
    @45
    @16
    @41
    @1
    cF
    fveq2
    negeqd
    eqeq12d
    imbi12d
    @43
    @44
    @49
    @46
    @43
    @42
    @49
    cc
    wcel
    @44
    @49
    wceq
    wph
    @42
    simpr
    #
    @43
    cB
    neglimc.b
    negcld
    #
    vx
    cA
    @49
    cc
    cG
    neglimc.g
    fvmpt2
    syl2anc
    @43
    @45
    cB
    @43
    @42
    cB
    cc
    wcel
    @45
    cB
    wceq
    @52
    neglimc.b
    vx
    cA
    cB
    cc
    cF
    neglimc.f
    fvmpt2
    syl2anc
    negeqd
    eqtr4d
    chvar
    oveq1d
    @38
    @16
    cC
    wph
    cA
    cc
    @1
    cF
    @26
    ffvelrnda
    #
    wph
    @23
    @35
    @13
    adantr
    #
    negsubdi3d
    eqtr4d
    fveq2d
    @38
    @17
    @38
    @16
    cC
    @54
    @55
    subcld
    absnegd
    eqtrd
    adantr
    @38
    @19
    simpr
    eqbrtrd
    syl21anc
    3exp
    ralimdva
    reximdva
    mpd
    ralrimiva
    wph
    vy
    vw
    vv
    cA
    cD
    @0
    cG
    wph
    vx
    cA
    @49
    cc
    cG
    @53
    neglimc.g
    fmptd
    @27
    @32
    ellimc3
    mpbir2and
end
