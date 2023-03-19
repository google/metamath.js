include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "mettri.mm"
include "wceq.mm"
include "metsym.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "breqtrrd.mm"

theorem mettri3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R


  assert |- ( ( D e. ( Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D B ) <_ ( ( A D C ) + ( B D C ) ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    wa
    #
    cA
    cB
    cD
    co
    cA
    cC
    cD
    co
    #
    cC
    cB
    cD
    co
    #
    caddc
    co
    @5
    cB
    cC
    cD
    co
    #
    caddc
    co
    cle
    cA
    cB
    cC
    cD
    cX
    mettri
    @4
    @7
    @6
    @5
    caddc
    @0
    @2
    @3
    @7
    @6
    wceq
    @1
    cB
    cC
    cD
    cX
    metsym
    3adant3r1
    oveq2d
    breqtrrd
end
