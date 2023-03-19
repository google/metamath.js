include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "chdmm4i.mm"
include "fveq2i.mm"
include "choccli.mm"
include "chincli.mm"
include "pjococi.mm"
include "eqtr3i.mm"

theorem chdmj1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( _|_ ` ( A vH B ) ) = ( ( _|_ ` A ) i^i ( _|_ ` B ) )

  proof
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cin
    #
    cort
    cfv
    #
    cort
    cfv
    cA
    cB
    chj
    co
    #
    cort
    cfv
    @2
    @3
    @4
    cort
    cA
    cB
    ch0le.1
    chjcl.2
    chdmm4i
    fveq2i
    @2
    @0
    @1
    cA
    ch0le.1
    choccli
    cB
    chjcl.2
    choccli
    chincli
    pjococi
    eqtr3i
end
