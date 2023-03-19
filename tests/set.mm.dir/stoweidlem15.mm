include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wf.mm"
include "simpl.mm"
include "ffvelrnda.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "syl.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "mp2and.mm"
include "syl6eleq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "fveq2.mm"
include "cbvralv.mm"
include "rspccva.mm"
include "sylanbr.mm"
include "sylan.mm"
include "simpld.mm"
include "3jca.mm"

theorem stoweidlem15
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vh: setvar h
  let cG: class G
  let cI: class I
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem15.1: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem15.3: |- ( ph -> G : ( 1 ... M ) --> Q )
  assume stoweidlem15.4: |- ( ( ph /\ f e. A ) -> f : T --> RR )

  disjoint A f
  disjoint G f
  disjoint I f
  disjoint T f
  disjoint f ph
  disjoint h t
  disjoint G h
  disjoint G t
  disjoint A h
  disjoint I h
  disjoint I t
  disjoint T h
  disjoint T t
  disjoint Z h
  disjoint s t
  disjoint G s
  disjoint I s
  disjoint S s
  disjoint T s
  disjoint k x
  assert |- ( ( ( ph /\ I e. ( 1 ... M ) ) /\ S e. T ) -> ( ( ( G ` I ) ` S ) e. RR /\ 0 <_ ( ( G ` I ) ` S ) /\ ( ( G ` I ) ` S ) <_ 1 ) )

  proof
    wph
    cI
    c1
    cM
    cfz
    co
    #
    wcel
    #
    wa
    #
    cS
    cT
    wcel
    #
    wa
    #
    cS
    cI
    cG
    cfv
    #
    cfv
    #
    cr
    wcel
    cc0
    @6
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    @2
    cT
    cr
    cS
    @5
    @2
    wph
    @5
    cA
    wcel
    #
    cT
    cr
    @5
    wf
    #
    wph
    @1
    simpl
    @2
    @5
    cQ
    wcel
    @9
    wph
    @0
    cQ
    cI
    cG
    stoweidlem15.3
    ffvelrnda
    #
    @9
    @5
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
    vt
    cv
    #
    @12
    cfv
    #
    cle
    wbr
    #
    @16
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
    #
    vh
    cA
    crab
    #
    cQ
    @21
    vh
    @5
    cA
    elrabi
    stoweidlem15.1
    eleq2s
    syl
    #
    @2
    @9
    wph
    @9
    wa
    #
    @10
    wi
    #
    @23
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
    @26
    wf
    #
    wi
    @25
    vf
    @5
    cA
    @26
    @5
    wceq
    #
    @28
    @24
    @29
    @10
    @30
    @27
    @9
    wph
    @26
    @5
    cA
    eleq1
    anbi2d
    cT
    cr
    @26
    @5
    feq1
    imbi12d
    stoweidlem15.4
    vtoclg
    syl
    mp2and
    ffvelrnda
    @4
    @7
    @8
    @2
    cc0
    @15
    @5
    cfv
    #
    cle
    wbr
    #
    @31
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
    @3
    @7
    @8
    wa
    #
    @2
    cZ
    @5
    cfv
    #
    cc0
    wceq
    #
    @35
    @2
    @9
    @38
    @35
    wa
    #
    @2
    @5
    @22
    wcel
    @9
    @39
    wa
    @2
    @5
    cQ
    @22
    @11
    stoweidlem15.1
    syl6eleq
    @21
    @39
    vh
    @5
    cA
    @12
    @5
    wceq
    #
    @14
    @38
    @20
    @35
    @40
    @13
    @37
    cc0
    cZ
    @12
    @5
    fveq1
    eqeq1d
    @40
    @19
    @34
    vt
    cT
    @40
    @17
    @32
    @18
    @33
    @40
    @16
    @31
    cc0
    cle
    @15
    @12
    @5
    fveq1
    #
    breq2d
    @40
    @16
    @31
    c1
    cle
    @41
    breq1d
    anbi12d
    ralbidv
    anbi12d
    elrab
    sylib
    simprd
    simprd
    @35
    cc0
    vs
    cv
    #
    @5
    cfv
    #
    cle
    wbr
    #
    @43
    c1
    cle
    wbr
    #
    wa
    #
    vs
    cT
    wral
    @3
    @36
    @46
    @34
    vs
    vt
    cT
    @42
    @15
    wceq
    #
    @44
    @32
    @45
    @33
    @47
    @43
    @31
    cc0
    cle
    @42
    @15
    @5
    fveq2
    #
    breq2d
    @47
    @43
    @31
    c1
    cle
    @48
    breq1d
    anbi12d
    cbvralv
    @46
    @36
    vs
    cS
    cT
    @42
    cS
    wceq
    #
    @44
    @7
    @45
    @8
    @49
    @43
    @6
    cc0
    cle
    @42
    cS
    @5
    fveq2
    #
    breq2d
    @49
    @43
    @6
    c1
    cle
    @50
    breq1d
    anbi12d
    rspccva
    sylanbr
    sylan
    #
    simpld
    @4
    @7
    @8
    @51
    simprd
    3jca
end
