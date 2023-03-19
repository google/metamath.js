include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "choccli.mm"
include "chdmj1i.mm"
include "pjococi.mm"
include "ineq1i.mm"
include "eqtri.mm"

theorem chdmj2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( ( _|_ ` A ) vH B ) ) = ( A i^i ( _|_ ` B ) )

  proof
    cA
    cort
    cfv
    #
    cB
    chj
    co
    cort
    cfv
    @0
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cin
    cA
    @2
    cin
    @0
    cB
    cA
    ch0le.1
    choccli
    chjcl.2
    chdmj1i
    @1
    cA
    @2
    cA
    ch0le.1
    pjococi
    ineq1i
    eqtri
end
