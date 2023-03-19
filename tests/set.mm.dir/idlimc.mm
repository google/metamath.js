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
include "simpr.mm"
include "wceq.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "adantrl.mm"
include "ex.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nfne.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "neeq1.mm"
include "oveq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sselda.mm"
include "fmptd.mm"
include "ellimc3.mm"
include "mpbir2and.mm"

theorem idlimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume idlimc.a: |- ( ph -> A C_ CC )
  assume idlimc.f: |- F = ( x e. A |-> x )
  assume idlimc.x: |- ( ph -> X e. CC )

  disjoint A x
  disjoint X x
  disjoint ph x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> X e. ( F limCC X ) )

  proof
    wph
    cX
    cF
    cX
    climc
    co
    wcel
    cX
    cc
    wcel
    vz
    cv
    #
    cX
    wne
    #
    @0
    cX
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
    wa
    #
    @0
    cF
    cfv
    #
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    crp
    wrex
    #
    vw
    crp
    wral
    idlimc.x
    wph
    @14
    vw
    crp
    wph
    @10
    crp
    wcel
    #
    wa
    #
    @15
    @1
    @3
    @10
    clt
    wbr
    #
    wa
    #
    @11
    wi
    #
    vz
    cA
    wral
    #
    @14
    wph
    @15
    simpr
    @16
    vx
    cv
    #
    cX
    wne
    #
    @21
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    wa
    #
    @21
    cF
    cfv
    #
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    @20
    @16
    @31
    vx
    cA
    wph
    @21
    cA
    wcel
    #
    @31
    @15
    wph
    @32
    wa
    #
    @26
    @30
    @33
    @25
    @30
    @22
    @33
    @25
    wa
    @29
    @24
    @10
    clt
    @33
    @29
    @24
    wceq
    @25
    @33
    @28
    @23
    cabs
    @33
    @27
    @21
    cX
    cmin
    @33
    @32
    @32
    @27
    @21
    wceq
    wph
    @32
    simpr
    #
    @34
    vx
    cA
    @21
    cA
    cF
    idlimc.f
    fvmpt2
    syl2anc
    oveq1d
    fveq2d
    adantr
    @33
    @25
    simpr
    eqbrtrd
    adantrl
    ex
    adantlr
    ralrimiva
    @31
    @19
    vx
    vz
    cA
    @26
    @30
    vz
    @22
    @25
    vz
    vz
    @21
    cX
    vz
    @21
    nfcv
    vz
    cX
    nfcv
    nfne
    @25
    vz
    nfv
    nfan
    @30
    vz
    nfv
    nfim
    @18
    @11
    vx
    @18
    vx
    nfv
    vx
    @9
    @10
    clt
    vx
    @8
    cabs
    vx
    cabs
    nfcv
    vx
    @7
    cX
    cmin
    vx
    @0
    cF
    vx
    cF
    vx
    cA
    @21
    cmpt
    idlimc.f
    vx
    cA
    @21
    nfmpt1
    nfcxfr
    vx
    @0
    nfcv
    nffv
    vx
    cmin
    nfcv
    vx
    cX
    nfcv
    nfov
    nffv
    vx
    clt
    nfcv
    vx
    @10
    nfcv
    nfbr
    nfim
    @21
    @0
    wceq
    #
    @26
    @18
    @30
    @11
    @35
    @22
    @1
    @25
    @17
    @21
    @0
    cX
    neeq1
    @35
    @24
    @3
    @10
    clt
    @35
    @23
    @2
    cabs
    @21
    @0
    cX
    cmin
    oveq1
    fveq2d
    breq1d
    anbi12d
    @35
    @29
    @9
    @10
    clt
    @35
    @28
    @8
    cabs
    @35
    @27
    @7
    cX
    cmin
    @21
    @0
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    cbvral
    sylib
    @13
    @20
    vy
    @10
    crp
    @4
    @10
    wceq
    #
    @12
    @19
    vz
    cA
    @36
    @6
    @18
    @11
    @36
    @5
    @17
    @1
    @4
    @10
    @3
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    wph
    vw
    vy
    vz
    cA
    cX
    cX
    cF
    wph
    vx
    cA
    @21
    cc
    cF
    wph
    cA
    cc
    @21
    idlimc.a
    sselda
    idlimc.f
    fmptd
    idlimc.a
    idlimc.x
    ellimc3
    mpbir2and
end
