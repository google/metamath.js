include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "wsbc.mm"
include "csb.mm"
include "wb.mm"
include "wn.mm"
include "wceq.mm"
include "nne.mm"
include "sbcbii.mm"
include "a1i.mm"
include "sbcng.mm"
include "sbceqg.mm"
include "syl6bbr.mm"
include "3bitr3d.mm"
include "con4bid.mm"
include "sbcex.mm"
include "con3i.mm"
include "c0.mm"
include "csbprc.mm"
include "eqtr4d.mm"
include "sylibr.mm"
include "2falsed.mm"
include "pm2.61i.mm"

theorem sbcne12
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( [. A / x ]. B =/= C <-> [_ A / x ]_ B =/= [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    cB
    cC
    wne
    #
    vx
    cA
    wsbc
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    wne
    #
    wb
    @0
    @2
    @5
    @0
    @1
    wn
    #
    vx
    cA
    wsbc
    #
    cB
    cC
    wceq
    #
    vx
    cA
    wsbc
    #
    @2
    wn
    @5
    wn
    #
    @7
    @9
    wb
    @0
    @6
    @8
    vx
    cA
    cB
    cC
    nne
    sbcbii
    a1i
    @1
    vx
    cA
    cvv
    sbcng
    @0
    @9
    @3
    @4
    wceq
    #
    @10
    vx
    cA
    cB
    cC
    cvv
    sbceqg
    @3
    @4
    nne
    #
    syl6bbr
    3bitr3d
    con4bid
    @0
    wn
    #
    @2
    @5
    @2
    @0
    @1
    vx
    cA
    sbcex
    con3i
    @13
    @11
    @10
    @13
    @3
    c0
    @4
    vx
    cA
    cB
    csbprc
    vx
    cA
    cC
    csbprc
    eqtr4d
    @12
    sylibr
    2falsed
    pm2.61i
end
