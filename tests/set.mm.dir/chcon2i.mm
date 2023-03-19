include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "chsscon2i.mm"
include "chsscon1i.mm"
include "anbi12i.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem chcon2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A = ( _|_ ` B ) <-> B = ( _|_ ` A ) )

  proof
    cA
    cB
    cort
    cfv
    #
    wss
    #
    @0
    cA
    wss
    #
    wa
    cB
    cA
    cort
    cfv
    #
    wss
    #
    @3
    cB
    wss
    #
    wa
    cA
    @0
    wceq
    cB
    @3
    wceq
    @1
    @4
    @2
    @5
    cA
    cB
    ch0le.1
    chjcl.2
    chsscon2i
    cB
    cA
    chjcl.2
    ch0le.1
    chsscon1i
    anbi12i
    cA
    @0
    eqss
    cB
    @3
    eqss
    3bitr4i
end
