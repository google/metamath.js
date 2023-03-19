include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "c2nd.mm"
include "cfv.mm"
include "wsbc.mm"
include "c1st.mm"
include "wb.mm"
include "vex.mm"
include "op2ndd.mm"
include "eqcomd.mm"
include "sbceq1a.mm"
include "syl.mm"
include "op1std.mm"
include "bitr2d.mm"

theorem sbcopeq1a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( A = <. x , y >. -> ( [. ( 1st ` A ) / x ]. [. ( 2nd ` A ) / y ]. ph <-> ph ) )

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
    wph
    wph
    vy
    cA
    c2nd
    cfv
    #
    wsbc
    #
    @4
    vx
    cA
    c1st
    cfv
    #
    wsbc
    #
    @2
    @1
    @3
    wceq
    wph
    @4
    wb
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
    wph
    vy
    @3
    sbceq1a
    syl
    @2
    @0
    @5
    wceq
    @4
    @6
    wb
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
    @4
    vx
    @5
    sbceq1a
    syl
    bitr2d
end
