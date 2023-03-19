include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "xmettri2.mm"
include "syl13anc.mm"
include "wceq.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "breqtrd.mm"

theorem xmettri
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


  assert |- ( ( D e. ( *Met ` X ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D B ) <_ ( ( A D C ) +e ( C D B ) ) )

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
    cA
    cC
    cD
    co
    #
    @8
    cxad
    co
    cle
    @5
    @0
    @3
    @1
    @2
    @6
    @9
    cle
    wbr
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    cA
    cB
    cC
    cD
    cX
    xmettri2
    syl13anc
    @5
    @7
    @10
    @8
    cxad
    @5
    @0
    @3
    @1
    @7
    @10
    wceq
    @11
    @12
    @13
    cC
    cA
    cD
    cX
    xmetsym
    syl3anc
    oveq1d
    breqtrd
end
