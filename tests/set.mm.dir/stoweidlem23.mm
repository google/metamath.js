include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cneg.mm"
include "caddc.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "ancli.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "negsubd.mm"
include "mpteq2da.mm"
include "simpr.mm"
include "renegcld.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfneg.mm"
include "nfeq2.mm"
include "simpl.mm"
include "eleq1d.mm"
include "nfmpt1.mm"
include "stoweidlem8.mm"
include "mpd3an23.mm"
include "eqeltrrd.mm"
include "syl5eqel.mm"
include "subne0d.mm"
include "resubcld.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fvmptf.mm"
include "subidd.mm"
include "eqtrd.mm"
include "3netr4d.mm"
include "3jca.mm"

theorem stoweidlem23
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cH: class H
  let cZ: class Z
  let vk: setvar k
  assume stoweidlem23.1: |- F/ t ph
  assume stoweidlem23.2: |- F/_ t G
  assume stoweidlem23.3: |- H = ( t e. T |-> ( ( G ` t ) - ( G ` Z ) ) )
  assume stoweidlem23.4: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem23.5: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem23.6: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem23.7: |- ( ph -> S e. T )
  assume stoweidlem23.8: |- ( ph -> Z e. T )
  assume stoweidlem23.9: |- ( ph -> G e. A )
  assume stoweidlem23.10: |- ( ph -> ( G ` S ) =/= ( G ` Z ) )

  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint A f
  disjoint A g
  disjoint G f
  disjoint G g
  disjoint f ph
  disjoint g ph
  disjoint Z g
  disjoint Z t
  disjoint t x
  disjoint T x
  disjoint S t
  disjoint A x
  disjoint G x
  disjoint Z x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( H e. A /\ ( H ` S ) =/= ( H ` Z ) /\ ( H ` Z ) = 0 ) )

  proof
    wph
    cH
    cA
    wcel
    cS
    cH
    cfv
    #
    cZ
    cH
    cfv
    #
    wne
    @1
    cc0
    wceq
    wph
    cH
    vt
    cT
    vt
    cv
    #
    cG
    cfv
    #
    cZ
    cG
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cA
    stoweidlem23.3
    wph
    vt
    cT
    @3
    @4
    cneg
    #
    caddc
    co
    #
    cmpt
    #
    @6
    cA
    wph
    vt
    cT
    @8
    @5
    stoweidlem23.1
    wph
    @2
    cT
    wcel
    #
    wa
    #
    @3
    @4
    @11
    @3
    wph
    cT
    cr
    @2
    cG
    wph
    cG
    cA
    wcel
    #
    wph
    @12
    wa
    #
    cT
    cr
    cG
    wf
    #
    stoweidlem23.9
    wph
    @12
    stoweidlem23.9
    ancli
    wph
    vf
    cv
    #
    cA
    wcel
    #
    wa
    #
    cT
    cr
    @15
    wf
    #
    wi
    @13
    @14
    wi
    vf
    cG
    cA
    @15
    cG
    wceq
    #
    @17
    @13
    @18
    @14
    @19
    @16
    @12
    wph
    @15
    cG
    cA
    eleq1
    anbi2d
    cT
    cr
    @15
    cG
    feq1
    imbi12d
    stoweidlem23.4
    vtoclg
    sylc
    #
    ffvelrnda
    recnd
    @11
    @4
    wph
    @4
    cr
    wcel
    @10
    wph
    cT
    cr
    cZ
    cG
    @20
    stoweidlem23.8
    ffvelrnd
    #
    adantr
    recnd
    negsubd
    mpteq2da
    wph
    vt
    cT
    @3
    @2
    vt
    cT
    @7
    cmpt
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    @9
    cA
    wph
    vt
    cT
    @24
    @8
    stoweidlem23.1
    @11
    @23
    @7
    @3
    caddc
    @11
    @10
    @7
    cr
    wcel
    #
    @23
    @7
    wceq
    wph
    @10
    simpr
    wph
    @26
    @10
    wph
    @4
    @21
    renegcld
    #
    adantr
    vt
    cT
    @7
    cr
    @22
    @22
    eqid
    fvmpt2
    syl2anc
    oveq2d
    mpteq2da
    wph
    @12
    @22
    cA
    wcel
    #
    @25
    cA
    wcel
    stoweidlem23.9
    wph
    @26
    wph
    @26
    wa
    #
    @28
    @27
    wph
    @26
    @27
    ancli
    wph
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    vt
    cT
    @30
    cmpt
    #
    cA
    wcel
    #
    wi
    @29
    @28
    wi
    vx
    @7
    cr
    @30
    @7
    wceq
    #
    @32
    @29
    @34
    @28
    @35
    @31
    @26
    wph
    @30
    @7
    cr
    eleq1
    anbi2d
    @35
    @33
    @22
    cA
    @35
    vt
    cT
    @30
    @7
    vt
    @30
    @7
    vt
    @4
    vt
    cZ
    cG
    stoweidlem23.2
    vt
    cZ
    nfcv
    #
    nffv
    #
    nfneg
    nfeq2
    @35
    @10
    simpl
    mpteq2da
    eleq1d
    imbi12d
    stoweidlem23.6
    vtoclg
    sylc
    wph
    vt
    cA
    cT
    vf
    vg
    cG
    @22
    stoweidlem23.5
    stoweidlem23.2
    vt
    cT
    @7
    nfmpt1
    stoweidlem8
    mpd3an23
    eqeltrrd
    eqeltrrd
    syl5eqel
    wph
    cS
    cG
    cfv
    #
    @4
    cmin
    co
    #
    cc0
    @0
    @1
    wph
    @38
    @4
    wph
    @38
    wph
    cT
    cr
    cS
    cG
    @20
    stoweidlem23.7
    ffvelrnd
    #
    recnd
    wph
    @4
    @21
    recnd
    #
    stoweidlem23.10
    subne0d
    wph
    cS
    cT
    wcel
    @39
    cr
    wcel
    @0
    @39
    wceq
    stoweidlem23.7
    wph
    @38
    @4
    @40
    @21
    resubcld
    vt
    cS
    @5
    @39
    cT
    cH
    cr
    vt
    cS
    nfcv
    #
    vt
    @38
    @4
    cmin
    vt
    cS
    cG
    stoweidlem23.2
    @42
    nffv
    vt
    cmin
    nfcv
    #
    @37
    nfov
    @2
    cS
    wceq
    @3
    @38
    @4
    cmin
    @2
    cS
    cG
    fveq2
    oveq1d
    stoweidlem23.3
    fvmptf
    syl2anc
    wph
    @1
    @4
    @4
    cmin
    co
    #
    cc0
    wph
    cZ
    cT
    wcel
    @44
    cr
    wcel
    @1
    @44
    wceq
    stoweidlem23.8
    wph
    @4
    @4
    @21
    @21
    resubcld
    vt
    cZ
    @5
    @44
    cT
    cH
    cr
    @36
    vt
    @4
    @4
    cmin
    @37
    @43
    @37
    nfov
    @2
    cZ
    wceq
    @3
    @4
    @4
    cmin
    @2
    cZ
    cG
    fveq2
    oveq1d
    stoweidlem23.3
    fvmptf
    syl2anc
    wph
    @4
    @41
    subidd
    eqtrd
    #
    3netr4d
    @45
    3jca
end
