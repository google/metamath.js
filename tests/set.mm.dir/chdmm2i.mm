include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "choccli.mm"
include "chdmm1i.mm"
include "pjococi.mm"
include "oveq1i.mm"
include "eqtri.mm"

theorem chdmm2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( ( _|_ ` A ) i^i B ) ) = ( A vH ( _|_ ` B ) )

  proof
    cA
    cort
    cfv
    #
    cB
    cin
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
    chj
    co
    cA
    @2
    chj
    co
    @0
    cB
    cA
    ch0le.1
    choccli
    chjcl.2
    chdmm1i
    @1
    cA
    @2
    chj
    cA
    ch0le.1
    pjococi
    oveq1i
    eqtri
end
