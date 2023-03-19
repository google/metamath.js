include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wceq.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "c0h.mm"
include "cif.mm"
include "breq1.mm"
include "anbi2d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "h0elch.mm"
include "elimel.mm"
include "atcvat2i.mm"
include "dedth.mm"
include "3impib.mm"

theorem atcvat2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. HAtoms /\ C e. HAtoms ) -> ( ( -. B = C /\ A <oH ( B vH C ) ) -> A e. HAtoms ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    cB
    cC
    wceq
    wn
    #
    cA
    cB
    cC
    chj
    co
    #
    ccv
    wbr
    #
    wa
    #
    cA
    cat
    wcel
    #
    wi
    #
    @0
    @1
    @2
    wa
    #
    @8
    wi
    @9
    @3
    @0
    cA
    c0h
    cif
    #
    @4
    ccv
    wbr
    #
    wa
    #
    @10
    cat
    wcel
    #
    wi
    #
    wi
    cA
    c0h
    cA
    @10
    wceq
    #
    @8
    @14
    @9
    @15
    @6
    @12
    @7
    @13
    @15
    @5
    @11
    @3
    cA
    @10
    @4
    ccv
    breq1
    anbi2d
    cA
    @10
    cat
    eleq1
    imbi12d
    imbi2d
    @10
    cB
    cC
    cA
    c0h
    cch
    h0elch
    elimel
    atcvat2i
    dedth
    3impib
end
