include "cmt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "cme.mm"
include "wbr.mm"
include "msmet2.mm"
include "metrtri.mm"
include "sylan.mm"
include "simpr1.mm"
include "simpr3.mm"
include "ovresd.mm"
include "simpr2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "3brtr3d.mm"

theorem msrtri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. MetSp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( abs ` ( ( A D C ) - ( B D C ) ) ) <_ ( A D B ) )

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
    cC
    cD
    cX
    cX
    cxp
    cres
    #
    co
    #
    cB
    cC
    @6
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cB
    @6
    co
    #
    cA
    cC
    cD
    co
    #
    cB
    cC
    cD
    co
    #
    cmin
    co
    #
    cabs
    cfv
    cA
    cB
    cD
    co
    cle
    @0
    @6
    cX
    cme
    cfv
    wcel
    @4
    @10
    @11
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
    metrtri
    sylan
    @5
    @9
    @14
    cabs
    @5
    @7
    @12
    @8
    @13
    cmin
    @5
    cA
    cC
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
    simpr3
    #
    ovresd
    @5
    cB
    cC
    cD
    cX
    @0
    @1
    @2
    @3
    simpr2
    #
    @16
    ovresd
    oveq12d
    fveq2d
    @5
    cA
    cB
    cD
    cX
    @15
    @17
    ovresd
    3brtr3d
end
