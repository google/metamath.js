include "csslt.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "df-sslt.mm"
include "bropaex12.mm"
include "wceq.mm"
include "sseq1.mm"
include "raleq.mm"
include "3anbi13d.mm"
include "ralbidv.mm"
include "3anbi23d.mm"
include "brabg.mm"
include "biadan2.mm"

theorem brsslt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( A <<s B <-> ( ( A e. _V /\ B e. _V ) /\ ( A C_ No /\ B C_ No /\ A. x e. A A. y e. B x <s y ) ) )

  proof
    cA
    cB
    csslt
    wbr
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    cA
    csur
    wss
    #
    cB
    csur
    wss
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    w3a
    #
    va
    cv
    #
    csur
    wss
    #
    vb
    cv
    #
    csur
    wss
    #
    @2
    vy
    @8
    wral
    #
    vx
    @6
    wral
    #
    w3a
    #
    va
    vb
    cA
    cB
    csslt
    vx
    vy
    va
    vb
    df-sslt
    #
    bropaex12
    @12
    @0
    @9
    @10
    vx
    cA
    wral
    #
    w3a
    @5
    va
    vb
    cA
    cB
    cvv
    cvv
    csslt
    @6
    cA
    wceq
    @7
    @0
    @11
    @14
    @9
    @6
    cA
    csur
    sseq1
    @10
    vx
    @6
    cA
    raleq
    3anbi13d
    @8
    cB
    wceq
    #
    @9
    @1
    @14
    @4
    @0
    @8
    cB
    csur
    sseq1
    @15
    @10
    @3
    vx
    cA
    @2
    vy
    @8
    cB
    raleq
    ralbidv
    3anbi23d
    @13
    brabg
    biadan2
end
