include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "c1st.mm"
include "c2nd.mm"
include "cxp.mm"
include "crab.mm"
include "fgraphopab.mm"
include "w3a.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "eqeq12d.mm"
include "rabxp.mm"
include "df-3an.mm"
include "opabbii.mm"
include "eqtri.mm"
include "syl6eqr.mm"

theorem fgraphxp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b

  disjoint F x
  disjoint A x
  disjoint B x
  disjoint F a
  disjoint F b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- ( F : A --> B -> F = { x e. ( A X. B ) | ( F ` ( 1st ` x ) ) = ( 2nd ` x ) } )

  proof
    cA
    cB
    cF
    wf
    cF
    va
    cv
    #
    cA
    wcel
    #
    vb
    cv
    #
    cB
    wcel
    #
    wa
    @0
    cF
    cfv
    #
    @2
    wceq
    #
    wa
    #
    va
    vb
    copab
    #
    vx
    cv
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @8
    c2nd
    cfv
    #
    wceq
    #
    vx
    cA
    cB
    cxp
    crab
    #
    cA
    cB
    cF
    va
    vb
    fgraphopab
    @13
    @1
    @3
    @5
    w3a
    #
    va
    vb
    copab
    @7
    @12
    @5
    vx
    va
    vb
    cA
    cB
    @8
    @0
    @2
    cop
    wceq
    #
    @10
    @4
    @11
    @2
    @15
    @9
    @0
    cF
    @0
    @2
    @8
    va
    vex
    #
    vb
    vex
    #
    op1std
    fveq2d
    @0
    @2
    @8
    @16
    @17
    op2ndd
    eqeq12d
    rabxp
    @14
    @6
    va
    vb
    @1
    @3
    @5
    df-3an
    opabbii
    eqtri
    syl6eqr
end
