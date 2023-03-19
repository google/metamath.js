include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cxad.mm"
include "caddc.mm"
include "cle.mm"
include "cxmt.mm"
include "wbr.mm"
include "metxmet.mm"
include "xmettri2.mm"
include "sylan.mm"
include "cr.mm"
include "wceq.mm"
include "metcl.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "breqtrd.mm"

theorem mettri2
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


  assert |- ( ( D e. ( Met ` X ) /\ ( C e. X /\ A e. X /\ B e. X ) ) -> ( A D B ) <_ ( ( C D A ) + ( C D B ) ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cC
    cX
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
    cxad
    co
    #
    @7
    @8
    caddc
    co
    #
    cle
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    @4
    @6
    @9
    cle
    wbr
    cD
    cX
    metxmet
    cA
    cB
    cC
    cD
    cX
    xmettri2
    sylan
    @5
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @9
    @10
    wceq
    @0
    @1
    @2
    @11
    @3
    cC
    cA
    cD
    cX
    metcl
    3adant3r3
    @0
    @1
    @3
    @12
    @2
    cC
    cB
    cD
    cX
    metcl
    3adant3r2
    @7
    @8
    rexadd
    syl2anc
    breqtrd
end
