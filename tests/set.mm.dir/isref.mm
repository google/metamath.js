include "wcel.mm"
include "cref.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "refrel.mm"
include "brrelex2i.mm"
include "anim2i.mm"
include "simpl.mm"
include "cuni.mm"
include "simpr.mm"
include "3eqtr3g.mm"
include "uniexg.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "adantrr.mm"
include "jca.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "raleq.mm"
include "anbi12d.mm"
include "eqeq1d.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "df-ref.mm"
include "brabg.mm"
include "pm5.21nd.mm"

theorem isref
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume isref.1: |- X = U. A
  assume isref.2: |- Y = U. B

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a b
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint a y
  disjoint B a
  disjoint b y
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( A e. C -> ( A Ref B <-> ( Y = X /\ A. x e. A E. y e. B x C_ y ) ) )

  proof
    cA
    cC
    wcel
    #
    cA
    cB
    cref
    wbr
    #
    cY
    cX
    wceq
    #
    vx
    cv
    vy
    cv
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    @0
    cB
    cvv
    wcel
    #
    wa
    @1
    @7
    @0
    cA
    cB
    cref
    refrel
    brrelex2i
    anim2i
    @0
    @6
    wa
    @0
    @7
    @0
    @6
    simpl
    @0
    @2
    @7
    @5
    @0
    @2
    wa
    #
    cB
    cuni
    #
    cvv
    wcel
    @7
    @8
    @9
    cA
    cuni
    #
    cvv
    @8
    cY
    cX
    @9
    @10
    @0
    @2
    simpr
    isref.2
    isref.1
    3eqtr3g
    @0
    @10
    cvv
    wcel
    @2
    cA
    cC
    uniexg
    adantr
    eqeltrd
    cB
    uniexb
    sylibr
    adantrr
    jca
    vb
    cv
    #
    cuni
    #
    va
    cv
    #
    cuni
    #
    wceq
    #
    @3
    vy
    @11
    wrex
    #
    vx
    @13
    wral
    #
    wa
    @12
    cX
    wceq
    #
    @16
    vx
    cA
    wral
    #
    wa
    @6
    va
    vb
    cA
    cB
    cC
    cvv
    cref
    @13
    cA
    wceq
    #
    @15
    @18
    @17
    @19
    @20
    @14
    cX
    @12
    @20
    @14
    @10
    cX
    @13
    cA
    unieq
    isref.1
    syl6eqr
    eqeq2d
    @16
    vx
    @13
    cA
    raleq
    anbi12d
    @11
    cB
    wceq
    #
    @18
    @2
    @19
    @5
    @21
    @12
    cY
    cX
    @21
    @12
    @9
    cY
    @11
    cB
    unieq
    isref.2
    syl6eqr
    eqeq1d
    @21
    @16
    @4
    vx
    cA
    @3
    vy
    @11
    cB
    rexeq
    ralbidv
    anbi12d
    va
    vb
    vx
    vy
    df-ref
    brabg
    pm5.21nd
end
