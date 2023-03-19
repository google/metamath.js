include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "cv.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "chil.mm"
include "shel.mm"
include "anim12i.mm"
include "an4s.mm"
include "ax-hvcom.mm"
include "syl.mm"
include "eqeq2d.mm"
include "2rexbidva.mm"
include "rexcom.mm"
include "syl6bb.mm"
include "shsel.mm"
include "wb.mm"
include "ancoms.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem shscom
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A +H B ) = ( B +H A ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    #
    vx
    cA
    cB
    cph
    co
    #
    cB
    cA
    cph
    co
    #
    @2
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    cB
    wrex
    vy
    cA
    wrex
    #
    @5
    @7
    @6
    cva
    co
    #
    wceq
    #
    vy
    cA
    wrex
    vz
    cB
    wrex
    #
    @5
    @3
    wcel
    @5
    @4
    wcel
    #
    @2
    @10
    @12
    vz
    cB
    wrex
    vy
    cA
    wrex
    @13
    @2
    @9
    @12
    vy
    vz
    cA
    cB
    @2
    @6
    cA
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    wa
    #
    @8
    @11
    @5
    @17
    @6
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    wa
    #
    @8
    @11
    wceq
    @0
    @15
    @1
    @16
    @20
    @0
    @15
    wa
    @18
    @1
    @16
    wa
    @19
    @6
    cA
    shel
    @7
    cB
    shel
    anim12i
    an4s
    @6
    @7
    ax-hvcom
    syl
    eqeq2d
    2rexbidva
    @12
    vy
    vz
    cA
    cB
    rexcom
    syl6bb
    vy
    vz
    cA
    cB
    @5
    shsel
    @1
    @0
    @14
    @13
    wb
    vz
    vy
    cB
    cA
    @5
    shsel
    ancoms
    3bitr4d
    eqrdv
end
