include "wss.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "chsscon3i.mm"
include "anbi12i.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem chcon3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A = B <-> ( _|_ ` B ) = ( _|_ ` A ) )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    cA
    cB
    wceq
    @2
    @3
    wceq
    @0
    @4
    @1
    @5
    cA
    cB
    ch0le.1
    chjcl.2
    chsscon3i
    cB
    cA
    chjcl.2
    ch0le.1
    chsscon3i
    anbi12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3bitr4i
end
