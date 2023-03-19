include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "sumeq2sdv.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cr.mm"
include "simpr.mm"
include "nnrecred.mm"
include "adantr.mm"
include "fzfid.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "stoweidlem15.mm"
include "simp1d.mm"
include "an32s.mm"
include "fsumrecl.mm"
include "remulcld.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "vtoclg.mm"
include "anabsi7.mm"

theorem stoweidlem30
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem30.1: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem30.2: |- P = ( t e. T |-> ( ( 1 / M ) x. sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) ) )
  assume stoweidlem30.3: |- ( ph -> M e. NN )
  assume stoweidlem30.4: |- ( ph -> G : ( 1 ... M ) --> Q )
  assume stoweidlem30.5: |- ( ( ph /\ f e. A ) -> f : T --> RR )

  disjoint f i
  disjoint T f
  disjoint T i
  disjoint A f
  disjoint G f
  disjoint f ph
  disjoint i ph
  disjoint h i
  disjoint h t
  disjoint T h
  disjoint i t
  disjoint T t
  disjoint A h
  disjoint G h
  disjoint G t
  disjoint Z h
  disjoint M i
  disjoint M t
  disjoint S i
  disjoint i s
  disjoint s t
  disjoint M s
  disjoint S s
  disjoint G s
  disjoint P s
  disjoint T s
  disjoint ph s
  disjoint k x
  assert |- ( ( ph /\ S e. T ) -> ( P ` S ) = ( ( 1 / M ) x. sum_ i e. ( 1 ... M ) ( ( G ` i ) ` S ) ) )

  proof
    wph
    cS
    cT
    wcel
    #
    cS
    cP
    cfv
    #
    c1
    cM
    cdiv
    co
    #
    c1
    cM
    cfz
    co
    #
    cS
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
    wceq
    #
    wph
    vs
    cv
    #
    cT
    wcel
    #
    wa
    #
    @10
    cP
    cfv
    #
    @2
    @3
    @10
    @5
    cfv
    #
    vi
    csu
    #
    cmul
    co
    #
    wceq
    #
    wi
    wph
    @0
    wa
    #
    @9
    wi
    vs
    cS
    cT
    @10
    cS
    wceq
    #
    @12
    @18
    @17
    @9
    @19
    @11
    @0
    wph
    @10
    cS
    cT
    eleq1
    anbi2d
    @19
    @13
    @1
    @16
    @8
    @10
    cS
    cP
    fveq2
    @19
    @15
    @7
    @2
    cmul
    @19
    @3
    @14
    @6
    vi
    @10
    cS
    @5
    fveq2
    sumeq2sdv
    oveq2d
    eqeq12d
    imbi12d
    @12
    @11
    @16
    cr
    wcel
    @17
    wph
    @11
    simpr
    @12
    @2
    @15
    wph
    @2
    cr
    wcel
    @11
    wph
    cM
    stoweidlem30.3
    nnrecred
    adantr
    @12
    @3
    @14
    vi
    @12
    c1
    cM
    fzfid
    wph
    @4
    @3
    wcel
    #
    @11
    @14
    cr
    wcel
    #
    wph
    @20
    wa
    @11
    wa
    @21
    cc0
    @14
    cle
    wbr
    @14
    c1
    cle
    wbr
    wph
    vt
    cA
    cQ
    @10
    cT
    vf
    vh
    cG
    @4
    cM
    cZ
    stoweidlem30.1
    stoweidlem30.4
    stoweidlem30.5
    stoweidlem15
    simp1d
    an32s
    fsumrecl
    remulcld
    vt
    @10
    @2
    @3
    vt
    cv
    #
    @5
    cfv
    #
    vi
    csu
    #
    cmul
    co
    @16
    cT
    cr
    cP
    @22
    @10
    wceq
    #
    @24
    @15
    @2
    cmul
    @25
    @3
    @23
    @14
    vi
    @22
    @10
    @5
    fveq2
    sumeq2sdv
    oveq2d
    stoweidlem30.2
    fvmptg
    syl2anc
    vtoclg
    anabsi7
end
