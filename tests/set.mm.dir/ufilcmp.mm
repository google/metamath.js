include "cufl.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wa.mm"
include "ccmp.mm"
include "cv.mm"
include "cfcls.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cufil.mm"
include "wral.mm"
include "cflim.mm"
include "cuni.mm"
include "cfil.mm"
include "ufilfil.mm"
include "eqid.mm"
include "fclscmpi.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "wb.mm"
include "toponuni.mm"
include "fveq2d.mm"
include "raleqdv.mm"
include "adantl.mm"
include "syl5ibr.mm"
include "wss.mm"
include "wrex.mm"
include "ufli.mm"
include "adantlr.mm"
include "r19.29.mm"
include "wi.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprr.mm"
include "fclsss2.mm"
include "syl3anc.mm"
include "ssn0.mm"
include "ex.mm"
include "syl.mm"
include "expr.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mpan2d.mm"
include "ralrimdva.mm"
include "fclscmp.mm"
include "sylibrd.mm"
include "impbid.mm"
include "uffclsflim.mm"
include "neeq1d.mm"
include "ralbiia.mm"
include "syl6bb.mm"

theorem ufilcmp
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vn: setvar n
  let vo: setvar o
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vy: setvar y
  let cL: class L
  let cN: class N
  let cF: class F
  let cY: class Y
  let cS: class S

  disjoint J f
  disjoint X f
  disjoint n o
  disjoint n x
  disjoint A n
  disjoint o x
  disjoint A o
  disjoint A x
  disjoint f g
  disjoint f j
  disjoint f n
  disjoint f o
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint g j
  disjoint g n
  disjoint g o
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j n
  disjoint j o
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n s
  disjoint n y
  disjoint J n
  disjoint o s
  disjoint o y
  disjoint J o
  disjoint s x
  disjoint s y
  disjoint J s
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint L f
  disjoint L g
  disjoint L j
  disjoint L n
  disjoint L o
  disjoint L s
  disjoint L x
  disjoint N n
  disjoint N s
  disjoint F f
  disjoint F g
  disjoint F n
  disjoint F o
  disjoint F s
  disjoint F x
  disjoint X g
  disjoint X j
  disjoint X n
  disjoint X o
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y j
  disjoint Y n
  disjoint Y o
  disjoint Y s
  disjoint Y x
  disjoint S s
  assert |- ( ( X e. UFL /\ J e. ( TopOn ` X ) ) -> ( J e. Comp <-> A. f e. ( UFil ` X ) ( J fLim f ) =/= (/) ) )

  proof
    cX
    cufl
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    wa
    #
    cJ
    ccmp
    wcel
    #
    cJ
    vf
    cv
    #
    cfcls
    co
    #
    c0
    wne
    #
    vf
    cX
    cufil
    cfv
    #
    wral
    #
    cJ
    @4
    cflim
    co
    #
    c0
    wne
    #
    vf
    @7
    wral
    @2
    @3
    @8
    @3
    @8
    @2
    @6
    vf
    cJ
    cuni
    #
    cufil
    cfv
    #
    wral
    #
    @3
    @6
    vf
    @12
    @4
    @12
    wcel
    @3
    @4
    @11
    cfil
    cfv
    wcel
    @6
    @4
    @11
    ufilfil
    @4
    cJ
    @11
    @11
    eqid
    fclscmpi
    sylan2
    ralrimiva
    @1
    @8
    @13
    wb
    @0
    @1
    @6
    vf
    @7
    @12
    @1
    cX
    @11
    cufil
    cX
    cJ
    toponuni
    fveq2d
    raleqdv
    adantl
    syl5ibr
    @2
    @8
    cJ
    vg
    cv
    #
    cfcls
    co
    #
    c0
    wne
    #
    vg
    cX
    cfil
    cfv
    #
    wral
    #
    @3
    @2
    @8
    @16
    vg
    @17
    @2
    @14
    @17
    wcel
    #
    wa
    #
    @8
    @14
    @4
    wss
    #
    vf
    @7
    wrex
    #
    @16
    @0
    @19
    @22
    @1
    vf
    @14
    cX
    ufli
    adantlr
    @8
    @22
    wa
    @6
    @21
    wa
    #
    vf
    @7
    wrex
    @20
    @16
    @6
    @21
    vf
    @7
    r19.29
    @20
    @23
    @16
    vf
    @7
    @20
    @4
    @7
    wcel
    #
    wa
    #
    @6
    @21
    @16
    @25
    @21
    @6
    @16
    @20
    @24
    @21
    @6
    @16
    wi
    #
    @20
    @24
    @21
    wa
    #
    wa
    #
    @5
    @15
    wss
    #
    @26
    @28
    @1
    @19
    @21
    @29
    @0
    @1
    @19
    @27
    simpllr
    @2
    @19
    @27
    simplr
    @20
    @24
    @21
    simprr
    @14
    @4
    cJ
    cX
    fclsss2
    syl3anc
    @29
    @6
    @16
    @5
    @15
    ssn0
    ex
    syl
    expr
    com23
    impd
    rexlimdva
    syl5
    mpan2d
    ralrimdva
    @1
    @3
    @18
    wb
    @0
    vg
    cJ
    cX
    fclscmp
    adantl
    sylibrd
    impbid
    @6
    @10
    vf
    @7
    @24
    @5
    @9
    c0
    @4
    cJ
    cX
    uffclsflim
    neeq1d
    ralbiia
    syl6bb
end
