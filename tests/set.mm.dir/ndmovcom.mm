include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "ndmov.mm"
include "wceq.mm"
include "ancom.mm"
include "sylnbi.mm"
include "eqtr4d.mm"

theorem ndmovcom
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  assume ndmov.1: |- dom F = ( S X. S )


  assert |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = ( B F A ) )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    wn
    cA
    cB
    cF
    co
    c0
    cB
    cA
    cF
    co
    #
    cA
    cB
    cS
    cF
    ndmov.1
    ndmov
    @2
    @1
    @0
    wa
    @3
    c0
    wceq
    @0
    @1
    ancom
    cB
    cA
    cS
    cF
    ndmov.1
    ndmov
    sylnbi
    eqtr4d
end
