include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "choccli.mm"
include "chdmm1i.mm"
include "pjococi.mm"
include "oveq2i.mm"
include "eqtri.mm"

theorem chdmm3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( A i^i ( _|_ ` B ) ) ) = ( ( _|_ ` A ) vH B )

  proof
    cA
    cB
    cort
    cfv
    #
    cin
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
    chj
    co
    @1
    cB
    chj
    co
    cA
    @0
    ch0le.1
    cB
    chjcl.2
    choccli
    chdmm1i
    @2
    cB
    @1
    chj
    cB
    chjcl.2
    pjococi
    oveq2i
    eqtri
end
