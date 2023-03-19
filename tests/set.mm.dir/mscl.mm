include "cmt.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "cr.mm"
include "wceq.mm"
include "ovres.mm"
include "3adant1.mm"
include "cme.mm"
include "cfv.mm"
include "msmet2.mm"
include "metcl.mm"
include "syl3an1.mm"
include "eqeltrrd.mm"

theorem mscl
  let cA: class A
  let cB: class B
  let cD: class D
  let cM: class M
  let cX: class X
  assume mscl.x: |- X = ( Base ` M )
  assume mscl.d: |- D = ( dist ` M )


  assert |- ( ( M e. MetSp /\ A e. X /\ B e. X ) -> ( A D B ) e. RR )

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
    cr
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
    cme
    cfv
    wcel
    @1
    @2
    @4
    cr
    wcel
    cD
    cM
    cX
    mscl.x
    mscl.d
    msmet2
    cA
    cB
    @3
    cX
    metcl
    syl3an1
    eqeltrrd
end
