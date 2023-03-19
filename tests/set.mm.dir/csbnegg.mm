include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "csb.mm"
include "cneg.mm"
include "csbov2g.mm"
include "df-neg.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbnegg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> [_ A / x ]_ -u B = -u [_ A / x ]_ B )

  proof
    cA
    cV
    wcel
    vx
    cA
    cc0
    cB
    cmin
    co
    #
    csb
    cc0
    vx
    cA
    cB
    csb
    #
    cmin
    co
    vx
    cA
    cB
    cneg
    #
    csb
    @1
    cneg
    vx
    cA
    cc0
    cB
    cmin
    cV
    csbov2g
    vx
    cA
    @2
    @0
    cB
    df-neg
    csbeq2i
    @1
    df-neg
    3eqtr4g
end
