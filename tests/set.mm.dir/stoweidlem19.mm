include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "wa.mm"
include "cr.mm"
include "cc.mm"
include "wf.mm"
include "ancli.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "recn.mm"
include "exp0.mm"
include "3syl.mm"
include "eqcomd.mm"
include "mpteq2da.mm"
include "1re.mm"
include "stoweidlem4.mm"
include "mpan2.mm"
include "eqeltrrd.mm"
include "simpr.mm"
include "simpll.mm"
include "simplr.mm"
include "mpd.mm"
include "w3a.mm"
include "cmul.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfel1.mm"
include "nf3an.mm"
include "simpl1.mm"
include "recnd.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "expp1d.mm"
include "3adant2.mm"
include "simp2.mm"
include "reexpcld.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "oveq1d.mm"
include "adantr.mm"
include "nfeq2.mm"
include "stoweidlem6.mm"
include "mpd3an3.mm"
include "eqeltrd.mm"
include "exp31.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem stoweidlem19
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  assume stoweidlem19.1: |- F/_ t F
  assume stoweidlem19.2: |- F/ t ph
  assume stoweidlem19.3: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem19.4: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem19.5: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem19.6: |- ( ph -> F e. A )
  assume stoweidlem19.7: |- ( ph -> N e. NN0 )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint F f
  disjoint F g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint N t
  disjoint t x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint f m
  disjoint g m
  disjoint m t
  disjoint A m
  disjoint F m
  disjoint T m
  disjoint m ph
  disjoint m n
  disjoint n t
  disjoint A n
  disjoint F n
  disjoint N n
  disjoint T n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( t e. T |-> ( ( F ` t ) ^ N ) ) e. A )

  proof
    cN
    cn0
    wcel
    wph
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    #
    cN
    cexp
    co
    #
    cmpt
    #
    cA
    wcel
    #
    stoweidlem19.7
    wph
    vt
    cT
    @1
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    vt
    cT
    @1
    cc0
    cexp
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    vt
    cT
    @1
    vm
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    #
    wph
    vt
    cT
    @1
    @12
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @4
    wi
    vn
    vm
    cN
    @5
    cc0
    wceq
    #
    @8
    @11
    wph
    @21
    @7
    @10
    cA
    @21
    vt
    cT
    @6
    @9
    @5
    cc0
    @1
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @5
    @12
    wceq
    #
    @8
    @15
    wph
    @22
    @7
    @14
    cA
    @22
    vt
    cT
    @6
    @13
    @5
    @12
    @1
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @5
    @17
    wceq
    #
    @8
    @20
    wph
    @23
    @7
    @19
    cA
    @23
    vt
    cT
    @6
    @18
    @5
    @17
    @1
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @5
    cN
    wceq
    #
    @8
    @4
    wph
    @24
    @7
    @3
    cA
    @24
    vt
    cT
    @6
    @2
    @5
    cN
    @1
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    wph
    vt
    cT
    c1
    cmpt
    #
    @10
    cA
    wph
    vt
    cT
    c1
    @9
    stoweidlem19.2
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @9
    c1
    @27
    @1
    cr
    wcel
    #
    @1
    cc
    wcel
    #
    @9
    c1
    wceq
    wph
    cT
    cr
    @0
    cF
    wph
    cF
    cA
    wcel
    #
    wph
    @30
    wa
    #
    cT
    cr
    cF
    wf
    #
    stoweidlem19.6
    wph
    @30
    stoweidlem19.6
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
    @33
    wf
    #
    wi
    @31
    @32
    wi
    vf
    cF
    cA
    @33
    cF
    wceq
    #
    @35
    @31
    @36
    @32
    @37
    @34
    @30
    wph
    @33
    cF
    cA
    eleq1
    anbi2d
    cT
    cr
    @33
    cF
    feq1
    imbi12d
    stoweidlem19.3
    vtoclg
    sylc
    ffvelrnda
    #
    @1
    recn
    @1
    exp0
    3syl
    eqcomd
    mpteq2da
    wph
    c1
    cr
    wcel
    @25
    cA
    wcel
    1re
    wph
    vx
    vt
    cA
    c1
    cT
    stoweidlem19.5
    stoweidlem4
    mpan2
    eqeltrrd
    @12
    cn0
    wcel
    #
    @16
    wph
    @20
    @39
    @16
    wa
    #
    wph
    wa
    #
    wph
    @39
    @15
    @20
    @40
    wph
    simpr
    #
    @39
    @16
    wph
    simpll
    @41
    wph
    @15
    @42
    @39
    @16
    wph
    simplr
    mpd
    wph
    @39
    @15
    w3a
    #
    @19
    vt
    cT
    @13
    @1
    cmul
    co
    #
    cmpt
    #
    cA
    @43
    vt
    cT
    @18
    @44
    wph
    @39
    @15
    vt
    stoweidlem19.2
    @39
    vt
    nfv
    vt
    @14
    cA
    vt
    cT
    @13
    nfmpt1
    #
    nfel1
    nf3an
    #
    @43
    @26
    wa
    #
    @1
    @12
    @48
    wph
    @26
    @29
    wph
    @39
    @15
    @26
    simpl1
    #
    @43
    @26
    simpr
    #
    @27
    @1
    @38
    recnd
    syl2anc
    wph
    @39
    @15
    @26
    simpl2
    #
    expp1d
    mpteq2da
    @43
    @45
    vt
    cT
    @0
    @14
    cfv
    #
    @1
    cmul
    co
    #
    cmpt
    #
    cA
    @43
    vt
    cT
    @44
    @53
    @47
    @48
    @13
    @52
    @1
    cmul
    @48
    @26
    @13
    cr
    wcel
    #
    @13
    @52
    wceq
    @50
    @48
    wph
    @39
    @26
    @55
    @49
    @51
    @50
    wph
    @39
    @26
    w3a
    @1
    @12
    wph
    @26
    @28
    @39
    @38
    3adant2
    wph
    @39
    @26
    simp2
    reexpcld
    syl3anc
    @26
    @55
    wa
    @52
    @13
    vt
    cT
    @13
    cr
    @14
    @14
    eqid
    fvmpt2
    eqcomd
    syl2anc
    oveq1d
    mpteq2da
    wph
    @15
    @54
    cA
    wcel
    #
    @39
    wph
    @15
    @30
    @56
    wph
    @30
    @15
    stoweidlem19.6
    adantr
    wph
    vt
    cA
    cT
    vf
    vg
    @14
    cF
    vt
    @33
    @14
    @46
    nfeq2
    vt
    vg
    cv
    cF
    stoweidlem19.1
    nfeq2
    stoweidlem19.4
    stoweidlem6
    mpd3an3
    3adant2
    eqeltrd
    eqeltrd
    syl3anc
    exp31
    nn0ind
    mpcom
end
