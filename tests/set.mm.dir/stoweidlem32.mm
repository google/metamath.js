include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cfz.mm"
include "csu.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "fveq2.mm"
include "sumeq2sdv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "adantl.mm"
include "simpr.mm"
include "fzfid.mm"
include "wf.mm"
include "simpl.mm"
include "ffvelrnda.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "syl.mm"
include "mp2and.mm"
include "adantlr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "fsumrecl.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "eqidd.mm"
include "eqtr4i.mm"
include "adantr.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "mpteq2da.mm"
include "syl5eq.mm"
include "stoweidlem20.mm"
include "stoweidlem4.mm"
include "mpdan.mm"
include "syl5eqel.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfeq2.mm"
include "stoweidlem6.mm"
include "mpd3an23.mm"

theorem stoweidlem32
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem32.1: |- F/ t ph
  assume stoweidlem32.2: |- P = ( t e. T |-> ( Y x. sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) ) )
  assume stoweidlem32.3: |- F = ( t e. T |-> sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) )
  assume stoweidlem32.4: |- H = ( t e. T |-> Y )
  assume stoweidlem32.5: |- ( ph -> M e. NN )
  assume stoweidlem32.6: |- ( ph -> Y e. RR )
  assume stoweidlem32.7: |- ( ph -> G : ( 1 ... M ) --> A )
  assume stoweidlem32.8: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem32.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem32.10: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem32.11: |- ( ( ph /\ f e. A ) -> f : T --> RR )

  disjoint f g
  disjoint f i
  disjoint f t
  disjoint G f
  disjoint g i
  disjoint g t
  disjoint G g
  disjoint i t
  disjoint G i
  disjoint G t
  disjoint A f
  disjoint A g
  disjoint F f
  disjoint F g
  disjoint T f
  disjoint T g
  disjoint T i
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint H g
  disjoint M i
  disjoint M t
  disjoint Y t
  disjoint t x
  disjoint T x
  disjoint A x
  disjoint Y x
  disjoint ph x
  disjoint i s
  disjoint s t
  disjoint G s
  disjoint M s
  disjoint T s
  disjoint Y s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> P e. A )

  proof
    wph
    cP
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    #
    @0
    cH
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cA
    wph
    cP
    vt
    cT
    cY
    c1
    cM
    cfz
    co
    #
    @0
    vi
    cv
    #
    cG
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmul
    co
    #
    cmpt
    @4
    stoweidlem32.2
    wph
    vt
    cT
    @10
    @3
    stoweidlem32.1
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @3
    @2
    @1
    cmul
    co
    @10
    @12
    @1
    @2
    @12
    @1
    @12
    @1
    @9
    cr
    @12
    vs
    @0
    @5
    vs
    cv
    #
    @7
    cfv
    #
    vi
    csu
    #
    @9
    cT
    cF
    cr
    cF
    vs
    cT
    @15
    cmpt
    #
    wceq
    @12
    cF
    vt
    cT
    @9
    cmpt
    #
    @16
    stoweidlem32.3
    vt
    vs
    cT
    @9
    @15
    @0
    @13
    wceq
    @5
    @8
    @14
    vi
    @0
    @13
    @7
    fveq2
    sumeq2sdv
    cbvmptv
    eqtri
    a1i
    @13
    @0
    wceq
    #
    @15
    @9
    wceq
    @12
    @18
    @5
    @14
    @8
    vi
    @13
    @0
    @7
    fveq2
    sumeq2sdv
    adantl
    wph
    @11
    simpr
    #
    @12
    @5
    @8
    vi
    @12
    c1
    cM
    fzfid
    @12
    @6
    @5
    wcel
    #
    wa
    cT
    cr
    @0
    @7
    wph
    @20
    cT
    cr
    @7
    wf
    #
    @11
    wph
    @20
    wa
    #
    wph
    @7
    cA
    wcel
    #
    @21
    wph
    @20
    simpl
    wph
    @5
    cA
    @6
    cG
    stoweidlem32.7
    ffvelrnda
    #
    @22
    @23
    wph
    @23
    wa
    #
    @21
    wi
    #
    @24
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
    @27
    wf
    #
    wi
    @26
    vf
    @7
    cA
    @27
    @7
    wceq
    #
    @29
    @25
    @30
    @21
    @31
    @28
    @23
    wph
    @27
    @7
    cA
    eleq1
    anbi2d
    cT
    cr
    @27
    @7
    feq1
    imbi12d
    stoweidlem32.11
    vtoclg
    syl
    mp2and
    adantlr
    wph
    @11
    @20
    simplr
    ffvelrnd
    fsumrecl
    #
    fvmptd
    #
    @32
    eqeltrd
    recnd
    @12
    @2
    @12
    @2
    cY
    cr
    @12
    vs
    @0
    cY
    cY
    cT
    cH
    cr
    cH
    vs
    cT
    cY
    cmpt
    #
    wceq
    @12
    cH
    vt
    cT
    cY
    cmpt
    #
    @34
    stoweidlem32.4
    vs
    vt
    cT
    cY
    cY
    @18
    cY
    eqidd
    cbvmptv
    eqtr4i
    a1i
    @12
    @18
    wa
    cY
    eqidd
    @19
    wph
    cY
    cr
    wcel
    #
    @11
    stoweidlem32.6
    adantr
    #
    fvmptd
    #
    @37
    eqeltrd
    recnd
    mulcomd
    @12
    @2
    cY
    @1
    @9
    cmul
    @38
    @33
    oveq12d
    eqtr2d
    mpteq2da
    syl5eq
    wph
    cF
    cA
    wcel
    cH
    cA
    wcel
    @4
    cA
    wcel
    wph
    vt
    cA
    cT
    vf
    vg
    vi
    cF
    cG
    cM
    stoweidlem32.1
    stoweidlem32.3
    stoweidlem32.5
    stoweidlem32.7
    stoweidlem32.8
    stoweidlem32.11
    stoweidlem20
    wph
    cH
    @35
    cA
    stoweidlem32.4
    wph
    @36
    @35
    cA
    wcel
    stoweidlem32.6
    wph
    vx
    vt
    cA
    cY
    cT
    stoweidlem32.10
    stoweidlem4
    mpdan
    syl5eqel
    wph
    vt
    cA
    cT
    vf
    vg
    cF
    cH
    vt
    @27
    cF
    vt
    cF
    @17
    stoweidlem32.3
    vt
    cT
    @9
    nfmpt1
    nfcxfr
    nfeq2
    vt
    vg
    cv
    cH
    vt
    cH
    @35
    stoweidlem32.4
    vt
    cT
    cY
    nfmpt1
    nfcxfr
    nfeq2
    stoweidlem32.9
    stoweidlem6
    mpd3an23
    eqeltrd
end
