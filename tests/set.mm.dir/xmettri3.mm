include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "xmettri.mm"
include "wceq.mm"
include "xmetsym.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "breqtrrd.mm"

theorem xmettri3
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


  assert |- ( ( D e. ( *Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D B ) <_ ( ( A D C ) +e ( B D C ) ) )

  proof
    cD
    cX
    cxmt
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
    cxad
    co
    @5
    cB
    cC
    cD
    co
    #
    cxad
    co
    cle
    cA
    cB
    cC
    cD
    cX
    xmettri
    @4
    @7
    @6
    @5
    cxad
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
    xmetsym
    3adant3r1
    oveq2d
    breqtrrd
end
