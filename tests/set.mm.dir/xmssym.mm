include "cxme.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cxmt.mm"
include "cfv.mm"
include "wceq.mm"
include "xmsxmet2.mm"
include "xmetsym.mm"
include "syl3an1.mm"
include "simp2.mm"
include "simp3.mm"
include "ovresd.mm"
include "3eqtr3d.mm"

theorem xmssym
  let cA: class A
  let cB: class B
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. *MetSp /\ A e. X /\ B e. X ) -> ( A D B ) = ( B D A ) )

  proof
    cM
    cxme
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
    cB
    cA
    @4
    co
    #
    cA
    cB
    cD
    co
    cB
    cA
    cD
    co
    @0
    @4
    cX
    cxmt
    cfv
    wcel
    @1
    @2
    @5
    @6
    wceq
    cD
    cM
    cX
    mscl.x
    mscl.d
    xmsxmet2
    cA
    cB
    @4
    cX
    xmetsym
    syl3an1
    @3
    cA
    cB
    cD
    cX
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    ovresd
    @3
    cB
    cA
    cD
    cX
    @8
    @7
    ovresd
    3eqtr3d
end
