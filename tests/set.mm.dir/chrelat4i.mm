include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cat.mm"
include "wral.mm"
include "wceq.mm"
include "wb.mm"
include "chrelat3i.mm"
include "anbi12i.mm"
include "eqss.mm"
include "ralbiim.mm"
include "3bitr4i.mm"

theorem chrelat4i
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chrelat3.1: |- A e. CH
  assume chrelat3.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A = B <-> A. x e. HAtoms ( x C_ A <-> x C_ B ) )

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
    vx
    cv
    #
    cA
    wss
    #
    @2
    cB
    wss
    #
    wi
    vx
    cat
    wral
    #
    @4
    @3
    wi
    vx
    cat
    wral
    #
    wa
    cA
    cB
    wceq
    @3
    @4
    wb
    vx
    cat
    wral
    @0
    @5
    @1
    @6
    vx
    cA
    cB
    chrelat3.1
    chrelat3.2
    chrelat3i
    vx
    cB
    cA
    chrelat3.2
    chrelat3.1
    chrelat3i
    anbi12i
    cA
    cB
    eqss
    @3
    @4
    vx
    cat
    ralbiim
    3bitr4i
end
