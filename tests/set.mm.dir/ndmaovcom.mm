include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "caov.mm"
include "cvv.mm"
include "cop.mm"
include "cdm.mm"
include "wceq.mm"
include "cxp.mm"
include "opelxp.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "bitr3i.mm"
include "ndmaov.mm"
include "sylnbi.mm"
include "ancom.mm"
include "3bitr2i.mm"
include "eqtr4d.mm"

theorem ndmaovcom
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume ndmaov.1: |- dom F = ( S X. S )


  assert |- ( -. ( A e. S /\ B e. S ) -> (( A F B )) = (( B F A )) )

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
    caov
    #
    cvv
    cB
    cA
    cF
    caov
    #
    @2
    cA
    cB
    cop
    #
    cF
    cdm
    #
    wcel
    #
    @3
    cvv
    wceq
    @2
    @5
    cS
    cS
    cxp
    #
    wcel
    @7
    cA
    cB
    cS
    cS
    opelxp
    @8
    @6
    @5
    @6
    @8
    ndmaov.1
    eqcomi
    #
    eleq2i
    bitr3i
    cA
    cB
    cF
    ndmaov
    sylnbi
    @2
    cB
    cA
    cop
    #
    @6
    wcel
    #
    @4
    cvv
    wceq
    @2
    @1
    @0
    wa
    @10
    @8
    wcel
    @11
    @0
    @1
    ancom
    cB
    cA
    cS
    cS
    opelxp
    @8
    @6
    @10
    @9
    eleq2i
    3bitr2i
    cB
    cA
    cF
    ndmaov
    sylnbi
    eqtr4d
end
