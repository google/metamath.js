include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "wi.mm"
include "shsel1.mm"
include "ancoms.mm"
include "shscom.mm"
include "eleq2d.mm"
include "sylibrd.mm"

theorem shsel2
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( C e. B -> C e. ( A +H B ) ) )

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
    cC
    cB
    wcel
    #
    cC
    cB
    cA
    cph
    co
    #
    wcel
    #
    cC
    cA
    cB
    cph
    co
    #
    wcel
    @1
    @0
    @3
    @5
    wi
    cB
    cA
    cC
    shsel1
    ancoms
    @2
    @6
    @4
    cC
    cA
    cB
    shscom
    eleq2d
    sylibrd
end
