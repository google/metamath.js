include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "caddc.mm"
include "nfel1.mm"
include "nf3an.mm"
include "wa.mm"
include "cneg.mm"
include "cmul.mm"
include "c1.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "wf.mm"
include "simpl1.mm"
include "neg1rr.mm"
include "stoweidlem4.mm"
include "mpan2.mm"
include "syl5eqel.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "mpdan.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "simpl3.mm"
include "3adant3.mm"
include "simp3.mm"
include "syl3anc.mm"
include "remulcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "adantl.mm"
include "oveq1d.mm"
include "recnd.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "simpl2.mm"
include "negsubd.mm"
include "eqtr2d.mm"
include "mpteq2da.mm"
include "3ad2ant1.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfeq2.mm"
include "stoweidlem6.mm"
include "syld3an2.mm"
include "stoweidlem8.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem stoweidlem22
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cL: class L
  let vk: setvar k
  assume stoweidlem22.8: |- F/ t ph
  assume stoweidlem22.9: |- F/_ t F
  assume stoweidlem22.10: |- F/_ t G
  assume stoweidlem22.1: |- H = ( t e. T |-> ( ( F ` t ) - ( G ` t ) ) )
  assume stoweidlem22.2: |- I = ( t e. T |-> -u 1 )
  assume stoweidlem22.3: |- L = ( t e. T |-> ( ( I ` t ) x. ( G ` t ) ) )
  assume stoweidlem22.4: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem22.5: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem22.6: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem22.7: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint I f
  disjoint I g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint L g
  disjoint t x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ( ph /\ F e. A /\ G e. A ) -> ( t e. T |-> ( ( F ` t ) - ( G ` t ) ) ) e. A )

  proof
    wph
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    w3a
    #
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    cmin
    co
    #
    cmpt
    vt
    cT
    @4
    @3
    cL
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    @2
    vt
    cT
    @6
    @8
    wph
    @0
    @1
    vt
    stoweidlem22.8
    vt
    cF
    cA
    stoweidlem22.9
    nfel1
    vt
    cG
    cA
    stoweidlem22.10
    nfel1
    nf3an
    @2
    @3
    cT
    wcel
    #
    wa
    #
    @8
    @4
    @5
    cneg
    #
    caddc
    co
    @6
    @11
    @7
    @12
    @4
    caddc
    @11
    @7
    @3
    cI
    cfv
    #
    @5
    cmul
    co
    #
    c1
    cneg
    #
    @5
    cmul
    co
    @12
    @11
    @10
    @14
    cr
    wcel
    @7
    @14
    wceq
    @2
    @10
    simpr
    #
    @11
    @13
    @5
    @11
    cT
    cr
    @3
    cI
    @11
    wph
    cT
    cr
    cI
    wf
    #
    wph
    @0
    @1
    @10
    simpl1
    #
    wph
    cI
    cA
    wcel
    #
    @17
    wph
    cI
    vt
    cT
    @15
    cmpt
    #
    cA
    stoweidlem22.2
    wph
    @15
    cr
    wcel
    #
    @20
    cA
    wcel
    neg1rr
    wph
    vx
    vt
    cA
    @15
    cT
    stoweidlem22.7
    stoweidlem4
    mpan2
    syl5eqel
    #
    wph
    @19
    @17
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
    @23
    wf
    #
    wi
    #
    wph
    @19
    wa
    #
    @17
    wi
    vf
    cI
    cA
    @23
    cI
    wceq
    #
    @25
    @28
    @26
    @17
    @29
    @24
    @19
    wph
    @23
    cI
    cA
    eleq1
    anbi2d
    cT
    cr
    @23
    cI
    feq1
    imbi12d
    stoweidlem22.4
    vtoclg
    anabsi7
    mpdan
    syl
    @16
    ffvelrnd
    @11
    wph
    @1
    @10
    @5
    cr
    wcel
    @18
    wph
    @0
    @1
    @10
    simpl3
    @16
    wph
    @1
    @10
    w3a
    cT
    cr
    @3
    cG
    wph
    @1
    cT
    cr
    cG
    wf
    #
    @10
    wph
    @1
    @30
    @27
    wph
    @1
    wa
    #
    @30
    wi
    vf
    cG
    cA
    @23
    cG
    wceq
    #
    @25
    @31
    @26
    @30
    @32
    @24
    @1
    wph
    @23
    cG
    cA
    eleq1
    anbi2d
    cT
    cr
    @23
    cG
    feq1
    imbi12d
    stoweidlem22.4
    vtoclg
    anabsi7
    3adant3
    wph
    @1
    @10
    simp3
    ffvelrnd
    syl3anc
    #
    remulcld
    vt
    cT
    @14
    cr
    cL
    stoweidlem22.3
    fvmpt2
    syl2anc
    @11
    @13
    @15
    @5
    cmul
    @10
    @13
    @15
    wceq
    #
    @2
    @10
    @21
    @34
    neg1rr
    vt
    cT
    @15
    cr
    cI
    stoweidlem22.2
    fvmpt2
    mpan2
    adantl
    oveq1d
    @11
    @5
    @11
    @5
    @33
    recnd
    #
    mulm1d
    3eqtrd
    oveq2d
    @11
    @4
    @5
    @11
    @4
    @11
    cT
    cr
    @3
    cF
    @11
    wph
    @0
    cT
    cr
    cF
    wf
    #
    @18
    wph
    @0
    @1
    @10
    simpl2
    wph
    @0
    @36
    @27
    wph
    @0
    wa
    #
    @36
    wi
    vf
    cF
    cA
    @23
    cF
    wceq
    #
    @25
    @37
    @26
    @36
    @38
    @24
    @0
    wph
    @23
    cF
    cA
    eleq1
    anbi2d
    cT
    cr
    @23
    cF
    feq1
    imbi12d
    stoweidlem22.4
    vtoclg
    anabsi7
    syl2anc
    @16
    ffvelrnd
    recnd
    @35
    negsubd
    eqtr2d
    mpteq2da
    wph
    @0
    @1
    cL
    cA
    wcel
    @9
    cA
    wcel
    @2
    cL
    vt
    cT
    @14
    cmpt
    #
    cA
    stoweidlem22.3
    wph
    @19
    @0
    @1
    @39
    cA
    wcel
    wph
    @0
    @19
    @1
    @22
    3ad2ant1
    wph
    vt
    cA
    cT
    vf
    vg
    cI
    cG
    vt
    @23
    cI
    vt
    cI
    @20
    stoweidlem22.2
    vt
    cT
    @15
    nfmpt1
    nfcxfr
    nfeq2
    vt
    vg
    cv
    cG
    stoweidlem22.10
    nfeq2
    stoweidlem22.6
    stoweidlem6
    syld3an2
    syl5eqel
    wph
    vt
    cA
    cT
    vf
    vg
    cF
    cL
    stoweidlem22.5
    stoweidlem22.9
    vt
    cL
    @39
    stoweidlem22.3
    vt
    cT
    @14
    nfmpt1
    nfcxfr
    stoweidlem8
    syld3an3
    eqeltrd
end
