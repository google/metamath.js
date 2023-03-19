include "csh.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "cv.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "ssrexv.mm"
include "adantl.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl3.mm"
include "shsel.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem shless
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( ( A e. SH /\ B e. SH /\ C e. SH ) /\ A C_ B ) -> ( A +H C ) C_ ( B +H C ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cC
    csh
    wcel
    #
    w3a
    #
    cA
    cB
    wss
    #
    wa
    #
    vx
    cA
    cC
    cph
    co
    #
    cB
    cC
    cph
    co
    #
    @5
    vx
    cv
    #
    vy
    cv
    vz
    cv
    cva
    co
    wceq
    vz
    cC
    wrex
    #
    vy
    cA
    wrex
    #
    @9
    vy
    cB
    wrex
    #
    @8
    @6
    wcel
    #
    @8
    @7
    wcel
    #
    @4
    @10
    @11
    wi
    @3
    @9
    vy
    cA
    cB
    ssrexv
    adantl
    @5
    @0
    @2
    @12
    @10
    wb
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl3
    #
    vy
    vz
    cA
    cC
    @8
    shsel
    syl2anc
    @5
    @1
    @2
    @13
    @11
    wb
    @0
    @1
    @2
    @4
    simpl2
    @14
    vy
    vz
    cB
    cC
    @8
    shsel
    syl2anc
    3imtr4d
    ssrdv
end
