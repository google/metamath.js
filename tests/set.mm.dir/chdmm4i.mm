include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "choccli.mm"
include "chdmm2i.mm"
include "pjococi.mm"
include "oveq2i.mm"
include "eqtri.mm"

theorem chdmm4i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( ( _|_ ` A ) i^i ( _|_ ` B ) ) ) = ( A vH B )

  proof
    cA
    cort
    cfv
    cB
    cort
    cfv
    #
    cin
    cort
    cfv
    cA
    @0
    cort
    cfv
    #
    chj
    co
    cA
    cB
    chj
    co
    cA
    @0
    ch0le.1
    cB
    chjcl.2
    choccli
    chdmm2i
    @1
    cB
    cA
    chj
    cB
    chjcl.2
    pjococi
    oveq2i
    eqtri
end
