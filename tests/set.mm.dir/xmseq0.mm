include "cxme.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "ovres.mm"
include "3adant1.mm"
include "eqeq1d.mm"
include "cxmt.mm"
include "cfv.mm"
include "wb.mm"
include "xmsxmet2.mm"
include "xmeteq0.mm"
include "syl3an1.mm"
include "bitr3d.mm"

theorem xmseq0
  let cA: class A
  let cB: class B
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. *MetSp /\ A e. X /\ B e. X ) -> ( ( A D B ) = 0 <-> A = B ) )

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
    cc0
    wceq
    #
    cA
    cB
    cD
    co
    #
    cc0
    wceq
    cA
    cB
    wceq
    #
    @3
    @5
    @7
    cc0
    @1
    @2
    @5
    @7
    wceq
    @0
    cA
    cB
    cX
    cX
    cD
    ovres
    3adant1
    eqeq1d
    @0
    @4
    cX
    cxmt
    cfv
    wcel
    @1
    @2
    @6
    @8
    wb
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
    xmeteq0
    syl3an1
    bitr3d
end
