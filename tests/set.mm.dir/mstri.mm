include "cmt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "cme.mm"
include "cfv.mm"
include "wbr.mm"
include "msmet2.mm"
include "mettri.mm"
include "sylan.mm"
include "simpr1.mm"
include "simpr2.mm"
include "ovresd.mm"
include "simpr3.mm"
include "oveq12d.mm"
include "3brtr3d.mm"

theorem mstri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. MetSp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D B ) <_ ( ( A D C ) + ( C D B ) ) )

  proof
    cM
    cmt
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
    cX
    cX
    cxp
    cres
    #
    co
    #
    cA
    cC
    @6
    co
    #
    cC
    cB
    @6
    co
    #
    caddc
    co
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
    cle
    @0
    @6
    cX
    cme
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
    msmet2
    cA
    cB
    cC
    @6
    cX
    mettri
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
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    ovresd
    @5
    @8
    @11
    @9
    @12
    caddc
    @5
    cA
    cC
    cD
    cX
    @13
    @0
    @1
    @2
    @3
    simpr3
    #
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
