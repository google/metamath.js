include "ccnv.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "cxp.mm"
include "cfv.mm"
include "elcnv2.mm"
include "fveq2.mm"
include "vex.mm"
include "opelvv.mm"
include "c2nd.mm"
include "c1st.mm"
include "op2ndd.mm"
include "op1std.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "copsex2gb.mm"
include "bitri.mm"

theorem elcnvlem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  assume elcnvlem.f: |- F = ( x e. ( _V X. _V ) |-> <. ( 2nd ` x ) , ( 1st ` x ) >. )


  assert |- ( A e. `' B <-> ( A e. ( _V X. _V ) /\ ( F ` A ) e. B ) )

  proof
    cA
    cB
    ccnv
    wcel
    cA
    vu
    cv
    #
    vv
    cv
    #
    cop
    #
    wceq
    #
    @1
    @0
    cop
    #
    cB
    wcel
    #
    wa
    vv
    wex
    vu
    wex
    cA
    cvv
    cvv
    cxp
    #
    wcel
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    wa
    vu
    vv
    cA
    cB
    elcnv2
    @8
    @5
    vu
    vv
    cA
    @3
    @7
    @4
    cB
    @3
    @7
    @2
    cF
    cfv
    #
    @4
    cA
    @2
    cF
    fveq2
    @2
    @6
    wcel
    @9
    @4
    wceq
    @0
    @1
    vu
    vex
    #
    vv
    vex
    #
    opelvv
    vx
    @2
    vx
    cv
    #
    c2nd
    cfv
    #
    @12
    c1st
    cfv
    #
    cop
    @4
    @6
    cF
    @12
    @2
    wceq
    @13
    @1
    @14
    @0
    @0
    @1
    @12
    @10
    @11
    op2ndd
    @0
    @1
    @12
    @10
    @11
    op1std
    opeq12d
    elcnvlem.f
    @1
    @0
    opex
    fvmpt
    ax-mp
    syl6eq
    eleq1d
    copsex2gb
    bitri
end
