include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "csb.mm"
include "cpr.mm"
include "csbun.mm"
include "csbsng.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "df-pr.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbprg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( C e. V -> [_ C / x ]_ { A , B } = { [_ C / x ]_ A , [_ C / x ]_ B } )

  proof
    cC
    cV
    wcel
    #
    vx
    cC
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    csb
    #
    vx
    cC
    cA
    csb
    #
    csn
    #
    vx
    cC
    cB
    csb
    #
    csn
    #
    cun
    #
    vx
    cC
    cA
    cB
    cpr
    #
    csb
    @5
    @7
    cpr
    @0
    @4
    vx
    cC
    @1
    csb
    #
    vx
    cC
    @2
    csb
    #
    cun
    @9
    vx
    cC
    @1
    @2
    csbun
    @0
    @11
    @6
    @12
    @8
    vx
    cC
    cA
    cV
    csbsng
    vx
    cC
    cB
    cV
    csbsng
    uneq12d
    syl5eq
    vx
    cC
    @10
    @3
    cA
    cB
    df-pr
    csbeq2i
    @5
    @7
    df-pr
    3eqtr4g
end
