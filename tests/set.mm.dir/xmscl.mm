include "cxme.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cxr.mm"
include "wceq.mm"
include "ovres.mm"
include "3adant1.mm"
include "cxmt.mm"
include "cfv.mm"
include "xmsxmet2.mm"
include "xmetcl.mm"
include "syl3an1.mm"
include "eqeltrrd.mm"

theorem xmscl
  let cA: class A
  let cB: class B
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. *MetSp /\ A e. X /\ B e. X ) -> ( A D B ) e. RR* )

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
    cB
    cD
    co
    #
    cxr
    @1
    @2
    @4
    @5
    wceq
    @0
    cA
    cB
    cX
    cX
    cD
    ovres
    3adant1
    @0
    @3
    cX
    cxmt
    cfv
    wcel
    @1
    @2
    @4
    cxr
    wcel
    cD
    cM
    cX
    mscl.x
    mscl.d
    xmsxmet2
    cA
    cB
    @3
    cX
    xmetcl
    syl3an1
    eqeltrrd
end
