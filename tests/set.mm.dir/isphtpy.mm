include "cphtpy.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cicc.mm"
include "wral.mm"
include "cii.mm"
include "chtpy.mm"
include "crab.mm"
include "ccn.mm"
include "cvv.mm"
include "ctop.mm"
include "cmpt2.mm"
include "cntop2.mm"
include "oveq2.mm"
include "oveqd.mm"
include "rabeq.mm"
include "syl.mm"
include "mpt2eq123dv.mm"
include "df-phtpy.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "oveq12.mm"
include "simpl.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "rabex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isphtpy
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let vj: setvar j
  assume isphtpy.2: |- ( ph -> F e. ( II Cn J ) )
  assume isphtpy.3: |- ( ph -> G e. ( II Cn J ) )

  disjoint F s
  disjoint G s
  disjoint H s
  disjoint J s
  disjoint ph s
  disjoint A s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint F g
  disjoint h s
  disjoint h t
  disjoint F h
  disjoint s t
  disjoint F t
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G t
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint H x
  disjoint H y
  disjoint K t
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint g j
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint h j
  disjoint J h
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint t x
  disjoint t y
  disjoint J t
  disjoint J x
  disjoint J y
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( H e. ( F ( PHtpy ` J ) G ) <-> ( H e. ( F ( II Htpy J ) G ) /\ A. s e. ( 0 [,] 1 ) ( ( 0 H s ) = ( F ` 0 ) /\ ( 1 H s ) = ( F ` 1 ) ) ) ) )

  proof
    wph
    cH
    cF
    cG
    cJ
    cphtpy
    cfv
    #
    co
    #
    wcel
    cH
    cc0
    vs
    cv
    #
    vh
    cv
    #
    co
    #
    cc0
    cF
    cfv
    #
    wceq
    #
    c1
    @2
    @3
    co
    #
    c1
    cF
    cfv
    #
    wceq
    #
    wa
    #
    vs
    cc0
    c1
    cicc
    co
    #
    wral
    #
    vh
    cF
    cG
    cii
    cJ
    chtpy
    co
    #
    co
    #
    crab
    #
    wcel
    cH
    @14
    wcel
    cc0
    @2
    cH
    co
    #
    @5
    wceq
    #
    c1
    @2
    cH
    co
    #
    @8
    wceq
    #
    wa
    #
    vs
    @11
    wral
    #
    wa
    wph
    @1
    @15
    cH
    wph
    vf
    vg
    cF
    cG
    cii
    cJ
    ccn
    co
    #
    @22
    @4
    cc0
    vf
    cv
    #
    cfv
    #
    wceq
    #
    @7
    c1
    @23
    cfv
    #
    wceq
    #
    wa
    #
    vs
    @11
    wral
    #
    vh
    @23
    vg
    cv
    #
    @13
    co
    #
    crab
    #
    @15
    @0
    cvv
    wph
    cF
    @22
    wcel
    cJ
    ctop
    wcel
    @0
    vf
    vg
    @22
    @22
    @32
    cmpt2
    #
    wceq
    isphtpy.2
    cF
    cii
    cJ
    cntop2
    vj
    cJ
    vf
    vg
    cii
    vj
    cv
    #
    ccn
    co
    #
    @35
    @29
    vh
    @23
    @30
    cii
    @34
    chtpy
    co
    #
    co
    #
    crab
    #
    cmpt2
    @33
    ctop
    cphtpy
    @34
    cJ
    wceq
    #
    vf
    vg
    @35
    @35
    @38
    @22
    @22
    @32
    @34
    cJ
    cii
    ccn
    oveq2
    #
    @40
    @39
    @37
    @31
    wceq
    @38
    @32
    wceq
    @39
    @36
    @13
    @23
    @30
    @34
    cJ
    cii
    chtpy
    oveq2
    oveqd
    @29
    vh
    @37
    @31
    rabeq
    syl
    mpt2eq123dv
    vj
    vf
    vg
    vh
    vs
    df-phtpy
    vf
    vg
    @22
    @22
    @32
    cii
    cJ
    ccn
    ovex
    #
    @41
    mpt2ex
    fvmpt
    3syl
    @23
    cF
    wceq
    #
    @30
    cG
    wceq
    #
    wa
    #
    @32
    @15
    wceq
    wph
    @44
    @29
    @12
    vh
    @31
    @14
    @23
    cF
    @30
    cG
    @13
    oveq12
    @44
    @28
    @10
    vs
    @11
    @44
    @25
    @6
    @27
    @9
    @44
    @24
    @5
    @4
    @44
    cc0
    @23
    cF
    @42
    @43
    simpl
    #
    fveq1d
    eqeq2d
    @44
    @26
    @8
    @7
    @44
    c1
    @23
    cF
    @45
    fveq1d
    eqeq2d
    anbi12d
    ralbidv
    rabeqbidv
    adantl
    isphtpy.2
    isphtpy.3
    @15
    cvv
    wcel
    wph
    @12
    vh
    @14
    cF
    cG
    @13
    ovex
    rabex
    a1i
    ovmpt2d
    eleq2d
    @12
    @21
    vh
    cH
    @14
    @3
    cH
    wceq
    #
    @10
    @20
    vs
    @11
    @46
    @6
    @17
    @9
    @19
    @46
    @4
    @16
    @5
    cc0
    @2
    @3
    cH
    oveq
    eqeq1d
    @46
    @7
    @18
    @8
    c1
    @2
    @3
    cH
    oveq
    eqeq1d
    anbi12d
    ralbidv
    elrab
    syl6bb
end
