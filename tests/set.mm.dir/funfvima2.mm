include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wcel.mm"
include "cfv.mm"
include "cima.mm"
include "wi.mm"
include "ssel.mm"
include "funfvima.mm"
include "ex.mm"
include "com23.mm"
include "a2d.mm"
include "syl5.mm"
include "imp.mm"

theorem funfvima2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A C_ dom F ) -> ( B e. A -> ( F ` B ) e. ( F " A ) ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    #
    cB
    cA
    wcel
    #
    cB
    cF
    cfv
    cF
    cA
    cima
    wcel
    #
    wi
    #
    @2
    @3
    cB
    @1
    wcel
    #
    wi
    @0
    @5
    cA
    @1
    cB
    ssel
    @0
    @3
    @6
    @4
    @0
    @6
    @3
    @4
    @0
    @6
    @5
    cA
    cB
    cF
    funfvima
    ex
    com23
    a2d
    syl5
    imp
end
