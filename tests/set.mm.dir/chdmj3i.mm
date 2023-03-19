include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "choccli.mm"
include "chdmj1i.mm"
include "pjococi.mm"
include "ineq2i.mm"
include "eqtri.mm"

theorem chdmj3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( A vH ( _|_ ` B ) ) ) = ( ( _|_ ` A ) i^i B )

  proof
    cA
    cB
    cort
    cfv
    #
    chj
    co
    cort
    cfv
    cA
    cort
    cfv
    #
    @0
    cort
    cfv
    #
    cin
    @1
    cB
    cin
    cA
    @0
    ch0le.1
    cB
    chjcl.2
    choccli
    chdmj1i
    @2
    cB
    @1
    cB
    chjcl.2
    pjococi
    ineq2i
    eqtri
end
