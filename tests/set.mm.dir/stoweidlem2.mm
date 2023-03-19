include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "adantr.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mpteq2da.mm"
include "wi.mm"
include "id.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "syl5eqel.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "3comr.mm"
include "3expib.mm"
include "eqeltrd.mm"

theorem stoweidlem2
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem2.1: |- F/ t ph
  assume stoweidlem2.2: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem2.3: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem2.4: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem2.5: |- ( ph -> E e. RR )
  assume stoweidlem2.6: |- ( ph -> F e. A )

  disjoint f g
  disjoint f t
  disjoint F f
  disjoint g t
  disjoint F g
  disjoint F t
  disjoint E f
  disjoint E t
  disjoint A f
  disjoint A g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint t x
  disjoint E x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint f s
  disjoint s t
  disjoint E s
  disjoint T s
  disjoint k x
  assert |- ( ph -> ( t e. T |-> ( E x. ( F ` t ) ) ) e. A )

  proof
    wph
    vt
    cT
    cE
    vt
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    vt
    cT
    @0
    vs
    cT
    cE
    cmpt
    #
    cfv
    #
    @1
    cmul
    co
    #
    cmpt
    #
    cA
    wph
    vt
    cT
    @2
    @5
    stoweidlem2.1
    wph
    @0
    cT
    wcel
    #
    wa
    #
    cE
    @4
    @1
    cmul
    @8
    @4
    cE
    @8
    @7
    cE
    cr
    wcel
    #
    @4
    cE
    wceq
    wph
    @7
    simpr
    wph
    @9
    @7
    stoweidlem2.5
    adantr
    vt
    cT
    cE
    cr
    @3
    vs
    vt
    cT
    cE
    cE
    vs
    cv
    @0
    wceq
    cE
    eqidd
    cbvmptv
    #
    fvmpt2
    syl2anc
    eqcomd
    oveq1d
    mpteq2da
    @3
    cA
    wcel
    wph
    @6
    cA
    wcel
    #
    wph
    @3
    vt
    cT
    cE
    cmpt
    #
    cA
    @10
    @9
    wph
    @12
    cA
    wcel
    #
    stoweidlem2.5
    wph
    vt
    cT
    vx
    cv
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @13
    wi
    vx
    cE
    cr
    @14
    cE
    wceq
    #
    @16
    @13
    wph
    @17
    @15
    @12
    cA
    @17
    vt
    cT
    @14
    cE
    @17
    id
    mpteq2dv
    eleq1d
    imbi2d
    wph
    @14
    cr
    wcel
    @16
    stoweidlem2.3
    expcom
    vtoclga
    mpcom
    syl5eqel
    wph
    vt
    cT
    @0
    vf
    cv
    #
    cfv
    #
    @1
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @11
    wi
    vf
    @3
    cA
    @18
    @3
    wceq
    #
    @22
    @11
    wph
    @23
    @21
    @6
    cA
    @23
    vt
    cT
    @20
    @5
    @23
    @19
    @4
    @1
    cmul
    @0
    @18
    @3
    fveq1
    oveq1d
    mpteq2dv
    eleq1d
    imbi2d
    wph
    @18
    cA
    wcel
    #
    @22
    cF
    cA
    wcel
    #
    wph
    @24
    wa
    #
    @22
    wph
    @25
    @24
    stoweidlem2.6
    adantr
    @26
    vt
    cT
    @19
    @0
    vg
    cv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @26
    @22
    wi
    vg
    cF
    cA
    @27
    cF
    wceq
    #
    @31
    @22
    @26
    @32
    @30
    @21
    cA
    @32
    vt
    cT
    @29
    @20
    @32
    @28
    @1
    @19
    cmul
    @0
    @27
    cF
    fveq1
    oveq2d
    mpteq2dv
    eleq1d
    imbi2d
    @27
    cA
    wcel
    #
    wph
    @24
    @31
    wph
    @24
    @33
    @31
    stoweidlem2.2
    3comr
    3expib
    vtoclga
    mpcom
    expcom
    vtoclga
    mpcom
    eqeltrd
end
