include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "mettri2.mm"
include "expcom.mm"
include "3coml.mm"
include "impcom.mm"
include "wceq.mm"
include "metsym.mm"
include "3adant3r2.mm"
include "oveq1d.mm"
include "breqtrrd.mm"

theorem mettri
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


  assert |- ( ( D e. ( Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D B ) <_ ( ( A D C ) + ( C D B ) ) )

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
    #
    wa
    #
    cA
    cB
    cD
    co
    #
    cC
    cA
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
    #
    cA
    cC
    cD
    co
    #
    @8
    caddc
    co
    cle
    @4
    @0
    @6
    @9
    cle
    wbr
    #
    @3
    @1
    @2
    @0
    @11
    wi
    @0
    @3
    @1
    @2
    w3a
    @11
    cA
    cB
    cC
    cD
    cX
    mettri2
    expcom
    3coml
    impcom
    @5
    @10
    @7
    @8
    caddc
    @0
    @1
    @3
    @10
    @7
    wceq
    @2
    cA
    cC
    cD
    cX
    metsym
    3adant3r2
    oveq1d
    breqtrrd
end
