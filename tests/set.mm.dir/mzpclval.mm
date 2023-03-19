include "cz.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "cfv.mm"
include "cmpt.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "cpw.mm"
include "crab.mm"
include "cvv.mm"
include "cmzpcl.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "pweqd.mm"
include "xpeq1d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "weq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "mpteq1d.mm"
include "raleqbi1dv.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "fveq1.mm"
include "cbvmptv.mm"
include "eleq1i.mm"
include "anbi12d.mm"
include "anbi1d.mm"
include "rabeqbidv.mm"
include "df-mzpcl.mm"
include "ovex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem mzpclval
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let cV: class V
  let vp: setvar p
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint V p
  disjoint V f
  disjoint V g
  disjoint f p
  disjoint g p
  disjoint f g
  disjoint V i
  disjoint i p
  disjoint V j
  disjoint V x
  disjoint j p
  disjoint p x
  disjoint j x
  disjoint V v
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint p v
  disjoint f v
  disjoint g v
  disjoint a v
  disjoint b v
  disjoint c v
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint a f
  disjoint b f
  disjoint c f
  disjoint a g
  disjoint b g
  disjoint c g
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint i v
  disjoint a i
  disjoint b i
  disjoint c i
  disjoint j v
  disjoint v x
  disjoint a j
  disjoint b j
  disjoint c j
  disjoint a x
  disjoint b x
  disjoint c x
  assert |- ( V e. _V -> ( mzPolyCld ` V ) = { p e. ~P ( ZZ ^m ( ZZ ^m V ) ) | ( ( A. i e. ZZ ( ( ZZ ^m V ) X. { i } ) e. p /\ A. j e. V ( x e. ( ZZ ^m V ) |-> ( x ` j ) ) e. p ) /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) } )

  proof
    vv
    cV
    cz
    vv
    cv
    #
    cmap
    co
    #
    va
    cv
    #
    csn
    #
    cxp
    #
    vp
    cv
    #
    wcel
    #
    va
    cz
    wral
    #
    vc
    @1
    vb
    cv
    #
    vc
    cv
    #
    cfv
    #
    cmpt
    #
    @5
    wcel
    #
    vb
    @0
    wral
    #
    wa
    #
    vf
    cv
    #
    vg
    cv
    #
    caddc
    cof
    co
    @5
    wcel
    @15
    @16
    cmul
    cof
    co
    @5
    wcel
    wa
    vg
    @5
    wral
    vf
    @5
    wral
    #
    wa
    #
    vp
    cz
    @1
    cmap
    co
    #
    cpw
    #
    crab
    cz
    cV
    cmap
    co
    #
    vi
    cv
    #
    csn
    #
    cxp
    #
    @5
    wcel
    #
    vi
    cz
    wral
    #
    vx
    @21
    vj
    cv
    #
    vx
    cv
    #
    cfv
    #
    cmpt
    #
    @5
    wcel
    #
    vj
    cV
    wral
    #
    wa
    #
    @17
    wa
    #
    vp
    cz
    @21
    cmap
    co
    #
    cpw
    #
    crab
    cvv
    cmzpcl
    @0
    cV
    wceq
    #
    @18
    @34
    vp
    @20
    @36
    @37
    @19
    @35
    @37
    @1
    @21
    cz
    cmap
    @0
    cV
    cz
    cmap
    oveq2
    #
    oveq2d
    pweqd
    @37
    @14
    @33
    @17
    @37
    @7
    @26
    @13
    @32
    @37
    @7
    @21
    @3
    cxp
    #
    @5
    wcel
    #
    va
    cz
    wral
    @26
    @37
    @6
    @40
    va
    cz
    @37
    @4
    @39
    @5
    @37
    @1
    @21
    @3
    @38
    xpeq1d
    eleq1d
    ralbidv
    @40
    @25
    va
    vi
    cz
    va
    vi
    weq
    #
    @39
    @24
    @5
    @41
    @3
    @23
    @21
    @2
    @22
    sneq
    xpeq2d
    eleq1d
    cbvralv
    syl6bb
    @37
    @13
    vc
    @21
    @10
    cmpt
    #
    @5
    wcel
    #
    vb
    cV
    wral
    @32
    @12
    @43
    vb
    @0
    cV
    @37
    @11
    @42
    @5
    @37
    vc
    @1
    @21
    @10
    @38
    mpteq1d
    eleq1d
    raleqbi1dv
    @43
    @31
    vb
    vj
    cV
    vb
    vj
    weq
    #
    @43
    vc
    @21
    @27
    @9
    cfv
    #
    cmpt
    #
    @5
    wcel
    @31
    @44
    @42
    @46
    @5
    @44
    vc
    @21
    @10
    @45
    @8
    @27
    @9
    fveq2
    mpteq2dv
    eleq1d
    @46
    @30
    @5
    vc
    vx
    @21
    @45
    @29
    @27
    @9
    @28
    fveq1
    cbvmptv
    eleq1i
    syl6bb
    cbvralv
    syl6bb
    anbi12d
    anbi1d
    rabeqbidv
    vc
    vv
    vf
    vg
    va
    vb
    vp
    df-mzpcl
    @34
    vp
    @36
    @35
    cz
    @21
    cmap
    ovex
    pwex
    rabex
    fvmpt
end
