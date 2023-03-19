include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "c2nd.mm"
include "cfv.mm"
include "csb.mm"
include "c1st.mm"
include "vex.mm"
include "op2ndd.mm"
include "eqcomd.mm"
include "csbeq1a.mm"
include "syl.mm"
include "op1std.mm"
include "eqtr2d.mm"

theorem csbopeq1a
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( A = <. x , y >. -> [_ ( 1st ` A ) / x ]_ [_ ( 2nd ` A ) / y ]_ B = B )

  proof
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    cB
    vy
    cA
    c2nd
    cfv
    #
    cB
    csb
    #
    vx
    cA
    c1st
    cfv
    #
    @4
    csb
    #
    @2
    @1
    @3
    wceq
    cB
    @4
    wceq
    @2
    @3
    @1
    @0
    @1
    cA
    vx
    vex
    #
    vy
    vex
    #
    op2ndd
    eqcomd
    vy
    @3
    cB
    csbeq1a
    syl
    @2
    @0
    @5
    wceq
    @4
    @6
    wceq
    @2
    @5
    @0
    @0
    @1
    cA
    @7
    @8
    op1std
    eqcomd
    vx
    @5
    @4
    csbeq1a
    syl
    eqtr2d
end
