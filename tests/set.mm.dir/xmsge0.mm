include "cxme.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cle.mm"
include "cxmt.mm"
include "cfv.mm"
include "wbr.mm"
include "xmsxmet2.mm"
include "xmetge0.mm"
include "syl3an1.mm"
include "wceq.mm"
include "ovres.mm"
include "3adant1.mm"
include "breqtrd.mm"

theorem xmsge0
  let cA: class A
  let cB: class B
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. *MetSp /\ A e. X /\ B e. X ) -> 0 <_ ( A D B ) )

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
    cc0
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
    cle
    @0
    @3
    cX
    cxmt
    cfv
    wcel
    @1
    @2
    cc0
    @4
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
    @3
    cX
    xmetge0
    syl3an1
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
    breqtrd
end
