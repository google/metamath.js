include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "chcon2i.mm"
include "eqcom.mm"
include "3bitr4i.mm"

theorem chcon1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( ( _|_ ` A ) = B <-> ( _|_ ` B ) = A )

  proof
    cB
    cA
    cort
    cfv
    #
    wceq
    cA
    cB
    cort
    cfv
    #
    wceq
    @0
    cB
    wceq
    @1
    cA
    wceq
    cB
    cA
    chjcl.2
    ch0le.1
    chcon2i
    @0
    cB
    eqcom
    @1
    cA
    eqcom
    3bitr4i
end
