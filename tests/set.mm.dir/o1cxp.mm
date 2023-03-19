include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmpt.mm"
include "cfv.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "ccxp.mm"
include "co.mm"
include "co1.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "cdm.mm"
include "o1f.mm"
include "syl.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "feq2d.mm"
include "mpbid.mm"
include "o1bdd.mm"
include "syl2anc.mm"
include "wa.mm"
include "cc0.mm"
include "cif.mm"
include "cre.mm"
include "cpi.mm"
include "cmul.mm"
include "ce.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "oveq1d.mm"
include "cvv.mm"
include "ovex.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "ad2ant2r.mm"
include "fveq2d.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "0re.mm"
include "ifcl.mm"
include "adantr.mm"
include "abscld.mm"
include "max2.mm"
include "sylancr.mm"
include "letrd.mm"
include "abscxpbnd.mm"
include "eqbrtrrd.mm"
include "expr.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "wss.mm"
include "o1mptrcl.mm"
include "cxpcld.mm"
include "fmptd.mm"
include "o1dm.mm"
include "eqsstr3d.mm"
include "simprl.mm"
include "max1.mm"
include "recld.mm"
include "recxpcld.mm"
include "pire.mm"
include "remulcl.mm"
include "reefcld.mm"
include "remulcld.mm"
include "elo12r.mm"
include "3expia.mm"
include "syl22anc.mm"
include "syld.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem o1cxp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  assume o1cxp.1: |- ( ph -> C e. CC )
  assume o1cxp.2: |- ( ph -> 0 <_ ( Re ` C ) )
  assume o1cxp.3: |- ( ( ph /\ x e. A ) -> B e. V )
  assume o1cxp.4: |- ( ph -> ( x e. A |-> B ) e. O(1) )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint C m
  disjoint C y
  disjoint C z
  disjoint m ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( x e. A |-> ( B ^c C ) ) e. O(1) )

  proof
    wph
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @1
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    cabs
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vm
    cr
    wrex
    vy
    cr
    wrex
    #
    vx
    cA
    cB
    cC
    ccxp
    co
    #
    cmpt
    #
    co1
    wcel
    #
    wph
    @3
    co1
    wcel
    #
    cA
    cc
    @3
    wf
    #
    @10
    o1cxp.4
    wph
    @3
    cdm
    #
    cc
    @3
    wf
    #
    @15
    wph
    @14
    @17
    o1cxp.4
    @3
    o1f
    syl
    wph
    @16
    cA
    cc
    @3
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @16
    cA
    wceq
    wph
    @18
    vx
    cA
    o1cxp.3
    ralrimiva
    vx
    cA
    cB
    cV
    dmmptg
    syl
    #
    feq2d
    mpbid
    #
    vy
    vz
    cA
    vm
    @3
    o1bdd
    syl2anc
    wph
    @9
    @13
    vy
    vm
    cr
    cr
    wph
    @0
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    #
    wa
    #
    @9
    @2
    @1
    @12
    cfv
    #
    cabs
    cfv
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cc0
    cif
    #
    cC
    cre
    cfv
    #
    ccxp
    co
    #
    cC
    cabs
    cfv
    #
    cpi
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    @13
    @24
    @8
    @36
    vz
    cA
    @24
    @1
    cA
    wcel
    #
    wa
    @7
    @35
    @2
    @24
    @38
    @7
    @35
    @24
    @38
    @7
    wa
    #
    wa
    #
    @4
    cC
    ccxp
    co
    #
    cabs
    cfv
    @26
    @34
    cle
    @40
    @41
    @25
    cabs
    wph
    @38
    @41
    @25
    wceq
    #
    @23
    @7
    wph
    @42
    vz
    cA
    wph
    vx
    cv
    #
    @3
    cfv
    #
    cC
    ccxp
    co
    #
    @43
    @12
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    @42
    vz
    cA
    wral
    wph
    @47
    vx
    cA
    wph
    @43
    cA
    wcel
    #
    wa
    #
    @45
    @11
    @46
    @49
    @44
    cB
    cC
    ccxp
    @49
    @48
    @18
    @44
    cB
    wceq
    wph
    @48
    simpr
    #
    o1cxp.3
    vx
    cA
    cB
    cV
    @3
    @3
    eqid
    fvmpt2
    syl2anc
    oveq1d
    @49
    @48
    @11
    cvv
    wcel
    @46
    @11
    wceq
    @50
    cB
    cC
    ccxp
    ovex
    vx
    cA
    @11
    cvv
    @12
    @12
    eqid
    #
    fvmpt2
    sylancl
    eqtr4d
    ralrimiva
    @47
    @42
    vx
    vz
    cA
    @47
    vz
    nfv
    vx
    @41
    @25
    vx
    @4
    cC
    ccxp
    vx
    cA
    cB
    @1
    nffvmpt1
    vx
    ccxp
    nfcv
    vx
    cC
    nfcv
    nfov
    vx
    cA
    @11
    @1
    nffvmpt1
    nfeq
    @43
    @1
    wceq
    #
    @45
    @41
    @46
    @25
    @52
    @44
    @4
    cC
    ccxp
    @43
    @1
    @3
    fveq2
    oveq1d
    @43
    @1
    @12
    fveq2
    eqeq12d
    cbvral
    sylib
    r19.21bi
    ad2ant2r
    fveq2d
    @40
    @4
    cC
    @28
    wph
    @38
    @4
    cc
    wcel
    @23
    @7
    wph
    cA
    cc
    @1
    @3
    @20
    ffvelrnda
    ad2ant2r
    #
    wph
    cC
    cc
    wcel
    #
    @23
    @39
    o1cxp.1
    ad2antrr
    wph
    cc0
    @29
    cle
    wbr
    @23
    @39
    o1cxp.2
    ad2antrr
    @24
    @28
    cr
    wcel
    #
    @39
    @24
    @22
    cc0
    cr
    wcel
    #
    @55
    wph
    @21
    @22
    simprr
    #
    0re
    @27
    @6
    cc0
    cr
    ifcl
    sylancl
    #
    adantr
    #
    @40
    @5
    @6
    @28
    @40
    @4
    @53
    abscld
    @24
    @22
    @39
    @57
    adantr
    @59
    @24
    @38
    @7
    simprr
    @24
    @6
    @28
    cle
    wbr
    #
    @39
    @24
    @56
    @22
    @60
    0re
    @57
    cc0
    @6
    max2
    sylancr
    adantr
    letrd
    abscxpbnd
    eqbrtrrd
    expr
    imim2d
    ralimdva
    @24
    cA
    cc
    @12
    wf
    #
    cA
    cr
    wss
    #
    @21
    @34
    cr
    wcel
    #
    @37
    @13
    wi
    wph
    @61
    @23
    wph
    vx
    cA
    @11
    cc
    @12
    @49
    cB
    cC
    wph
    vx
    cA
    cB
    cV
    o1cxp.3
    o1cxp.4
    o1mptrcl
    wph
    @54
    @48
    o1cxp.1
    adantr
    cxpcld
    @51
    fmptd
    adantr
    wph
    @62
    @23
    wph
    cA
    @16
    cr
    @19
    wph
    @14
    @16
    cr
    wss
    o1cxp.4
    @3
    o1dm
    syl
    eqsstr3d
    adantr
    wph
    @21
    @22
    simprl
    @24
    @30
    @33
    @24
    @28
    @29
    @58
    @24
    @56
    @22
    cc0
    @28
    cle
    wbr
    0re
    @57
    cc0
    @6
    max1
    sylancr
    @24
    cC
    wph
    @54
    @23
    o1cxp.1
    adantr
    #
    recld
    recxpcld
    @24
    @32
    @24
    @31
    cr
    wcel
    cpi
    cr
    wcel
    @32
    cr
    wcel
    @24
    cC
    @64
    abscld
    pire
    @31
    cpi
    remulcl
    sylancl
    reefcld
    remulcld
    @61
    @62
    wa
    @21
    @63
    wa
    @37
    @13
    vz
    cA
    @0
    @12
    @34
    elo12r
    3expia
    syl22anc
    syld
    rexlimdvva
    mpd
end
