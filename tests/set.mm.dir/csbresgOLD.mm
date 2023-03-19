include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "csb.mm"
include "cres.mm"
include "csbin.mm"
include "csbxp.mm"
include "csbconstg.mm"
include "xpeq2d.mm"
include "syl5eq.mm"
include "ineq2d.mm"
include "df-res.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbresgOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> [_ A / x ]_ ( B |` C ) = ( [_ A / x ]_ B |` [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cC
    cvv
    cxp
    #
    cin
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    cvv
    cxp
    #
    cin
    #
    vx
    cA
    cB
    cC
    cres
    #
    csb
    @4
    @5
    cres
    @0
    @3
    @4
    vx
    cA
    @1
    csb
    #
    cin
    @7
    vx
    cA
    cB
    @1
    csbin
    @0
    @9
    @6
    @4
    @0
    @9
    @5
    vx
    cA
    cvv
    csb
    #
    cxp
    @6
    vx
    cA
    cC
    cvv
    csbxp
    @0
    @10
    cvv
    @5
    vx
    cA
    cvv
    cV
    csbconstg
    xpeq2d
    syl5eq
    ineq2d
    syl5eq
    vx
    cA
    @8
    @2
    cB
    cC
    df-res
    csbeq2i
    @4
    @5
    df-res
    3eqtr4g
end
