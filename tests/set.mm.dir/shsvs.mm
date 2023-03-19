include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "w3a.mm"
include "cmv.mm"
include "shscl.mm"
include "a1d.mm"
include "shsel1.mm"
include "adantrd.mm"
include "shsel2.mm"
include "adantld.mm"
include "3jcad.mm"
include "shsubcl.mm"
include "syl6.mm"

theorem shsvs
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. SH /\ B e. SH ) -> ( ( C e. A /\ D e. B ) -> ( C -h D ) e. ( A +H B ) ) )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    wa
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    #
    cA
    cB
    cph
    co
    #
    csh
    wcel
    #
    cC
    @4
    wcel
    #
    cD
    @4
    wcel
    #
    w3a
    cC
    cD
    cmv
    co
    @4
    wcel
    @0
    @3
    @5
    @6
    @7
    @0
    @5
    @3
    cA
    cB
    shscl
    a1d
    @0
    @1
    @6
    @2
    cA
    cB
    cC
    shsel1
    adantrd
    @0
    @2
    @7
    @1
    cA
    cB
    cD
    shsel2
    adantld
    3jcad
    cC
    cD
    @4
    shsubcl
    syl6
end
