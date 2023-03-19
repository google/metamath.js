include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "cc0.mm"
include "wcel.mm"
include "wceq.mm"
include "stoweidlem30.mm"
include "mpdan.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprld.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "cuz.mm"
include "wss.mm"
include "wo.mm"
include "fzfi.mm"
include "olc.mm"
include "sumz.mm"
include "mp2b.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "reccld.mm"
include "mul01d.mm"
include "3eqtrd.mm"

theorem stoweidlem37
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem37.1: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem37.2: |- P = ( t e. T |-> ( ( 1 / M ) x. sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) ) )
  assume stoweidlem37.3: |- ( ph -> M e. NN )
  assume stoweidlem37.4: |- ( ph -> G : ( 1 ... M ) --> Q )
  assume stoweidlem37.5: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem37.6: |- ( ph -> Z e. T )

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
  disjoint Z i
  disjoint Z t
  disjoint M i
  disjoint M t
  disjoint k x
  assert |- ( ph -> ( P ` Z ) = 0 )

  proof
    wph
    cZ
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
    cZ
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
    @1
    cc0
    cmul
    co
    cc0
    wph
    cZ
    cT
    wcel
    @0
    @7
    wceq
    stoweidlem37.6
    wph
    vt
    cA
    cP
    cQ
    cZ
    cT
    vf
    vh
    vi
    cG
    cM
    cZ
    stoweidlem37.1
    stoweidlem37.2
    stoweidlem37.3
    stoweidlem37.4
    stoweidlem37.5
    stoweidlem30
    mpdan
    wph
    @6
    cc0
    @1
    cmul
    wph
    @6
    @2
    cc0
    vi
    csu
    #
    cc0
    wph
    @2
    @5
    cc0
    vi
    wph
    @3
    @2
    wcel
    wa
    #
    @4
    cA
    wcel
    #
    @5
    cc0
    wceq
    #
    cc0
    vt
    cv
    #
    @4
    cfv
    #
    cle
    wbr
    #
    @13
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @9
    @4
    cQ
    wcel
    @10
    @11
    @17
    wa
    #
    wa
    wph
    @2
    cQ
    @3
    cG
    stoweidlem37.4
    ffvelrnda
    cZ
    vh
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    cc0
    @12
    @19
    cfv
    #
    cle
    wbr
    #
    @22
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    wa
    @18
    vh
    @4
    cA
    cQ
    @19
    @4
    wceq
    #
    @21
    @11
    @26
    @17
    @27
    @20
    @5
    cc0
    cZ
    @19
    @4
    fveq1
    eqeq1d
    @27
    @25
    @16
    vt
    cT
    @27
    @23
    @14
    @24
    @15
    @27
    @22
    @13
    cc0
    cle
    @12
    @19
    @4
    fveq1
    #
    breq2d
    @27
    @22
    @13
    c1
    cle
    @28
    breq1d
    anbi12d
    ralbidv
    anbi12d
    stoweidlem37.1
    elrab2
    sylib
    simprld
    sumeq2dv
    @2
    cfn
    wcel
    #
    @2
    c1
    cuz
    cfv
    wss
    #
    @29
    wo
    @8
    cc0
    wceq
    c1
    cM
    fzfi
    @29
    @30
    olc
    @2
    vi
    c1
    sumz
    mp2b
    syl6eq
    oveq2d
    wph
    @1
    wph
    cM
    wph
    cM
    stoweidlem37.3
    nncnd
    wph
    cM
    stoweidlem37.3
    nnne0d
    reccld
    mul01d
    3eqtrd
end
