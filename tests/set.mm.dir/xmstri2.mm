include "cxme.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "cxmt.mm"
include "cfv.mm"
include "wbr.mm"
include "xmsxmet2.mm"
include "xmettri2.mm"
include "sylan.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ovresd.mm"
include "simpr1.mm"
include "oveq12d.mm"
include "3brtr3d.mm"

theorem xmstri2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. *MetSp /\ ( C e. X /\ A e. X /\ B e. X ) ) -> ( A D B ) <_ ( ( C D A ) +e ( C D B ) ) )

  proof
    cM
    cxme
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
    cX
    cX
    cxp
    cres
    #
    co
    #
    cC
    cA
    @6
    co
    #
    cC
    cB
    @6
    co
    #
    cxad
    co
    #
    cA
    cB
    cD
    co
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
    cle
    @0
    @6
    cX
    cxmt
    cfv
    wcel
    @4
    @7
    @10
    cle
    wbr
    cD
    cM
    cX
    mscl.x
    mscl.d
    xmsxmet2
    cA
    cB
    cC
    @6
    cX
    xmettri2
    sylan
    @5
    cA
    cB
    cD
    cX
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    ovresd
    @5
    @8
    @11
    @9
    @12
    cxad
    @5
    cC
    cA
    cD
    cX
    @0
    @1
    @2
    @3
    simpr1
    #
    @13
    ovresd
    @5
    cC
    cB
    cD
    cX
    @15
    @14
    ovresd
    oveq12d
    3brtr3d
end
