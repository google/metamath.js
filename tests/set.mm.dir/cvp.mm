include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "cin.mm"
include "ccv.mm"
include "wbr.mm"
include "c0h.mm"
include "wceq.mm"
include "chj.mm"
include "co.mm"
include "wb.mm"
include "atelch.mm"
include "chincl.mm"
include "sylan2.mm"
include "atcveq0.mm"
include "sylancom.mm"
include "cvexch.mm"
include "bitr3d.mm"

theorem cvp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( ( A i^i B ) = 0H <-> A <oH ( A vH B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    cA
    cB
    cin
    #
    cB
    ccv
    wbr
    #
    @2
    c0h
    wceq
    #
    cA
    cA
    cB
    chj
    co
    ccv
    wbr
    #
    @0
    @1
    @2
    cch
    wcel
    #
    @3
    @4
    wb
    @1
    @0
    cB
    cch
    wcel
    #
    @6
    cB
    atelch
    #
    cA
    cB
    chincl
    sylan2
    @2
    cB
    atcveq0
    sylancom
    @1
    @0
    @7
    @3
    @5
    wb
    @8
    cA
    cB
    cvexch
    sylan2
    bitr3d
end
