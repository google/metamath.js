include "chj.mm"
include "co.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "inass.mm"
include "chdmj1i.mm"
include "ineq1i.mm"
include "ineq2i.mm"
include "3eqtr4i.mm"
include "fveq2i.mm"
include "chjcli.mm"
include "chdmm4i.mm"
include "3eqtr3i.mm"

theorem chjassi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH
  assume chjass.3: |- C e. CH


  assert |- ( ( A vH B ) vH C ) = ( A vH ( B vH C ) )

  proof
    cA
    cB
    chj
    co
    #
    cort
    cfv
    #
    cC
    cort
    cfv
    #
    cin
    #
    cort
    cfv
    cA
    cort
    cfv
    #
    cB
    cC
    chj
    co
    #
    cort
    cfv
    #
    cin
    #
    cort
    cfv
    @0
    cC
    chj
    co
    cA
    @5
    chj
    co
    @3
    @7
    cort
    @4
    cB
    cort
    cfv
    #
    cin
    #
    @2
    cin
    @4
    @8
    @2
    cin
    #
    cin
    @3
    @7
    @4
    @8
    @2
    inass
    @1
    @9
    @2
    cA
    cB
    ch0le.1
    chjcl.2
    chdmj1i
    ineq1i
    @6
    @10
    @4
    cB
    cC
    chjcl.2
    chjass.3
    chdmj1i
    ineq2i
    3eqtr4i
    fveq2i
    @0
    cC
    cA
    cB
    ch0le.1
    chjcl.2
    chjcli
    chjass.3
    chdmm4i
    cA
    @5
    ch0le.1
    cB
    cC
    chjcl.2
    chjass.3
    chjcli
    chdmm4i
    3eqtr3i
end
