include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cxme.mm"
include "wceq.mm"
include "ngpxms.mm"
include "xmssym.mm"
include "syl3an1.mm"
include "ngpds.mm"
include "3com23.mm"
include "eqtrd.mm"

theorem ngpdsr
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume ngpds.n: |- N = ( norm ` G )
  assume ngpds.x: |- X = ( Base ` G )
  assume ngpds.m: |- .- = ( -g ` G )
  assume ngpds.d: |- D = ( dist ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( A D B ) = ( N ` ( B .- A ) ) )

  proof
    cG
    cngp
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
    co
    #
    cB
    cA
    cD
    co
    #
    cB
    cA
    c.mi
    co
    cN
    cfv
    #
    @0
    cG
    cxme
    wcel
    @1
    @2
    @3
    @4
    wceq
    cG
    ngpxms
    cA
    cB
    cD
    cG
    cX
    ngpds.x
    ngpds.d
    xmssym
    syl3an1
    @0
    @2
    @1
    @4
    @5
    wceq
    cB
    cA
    cD
    cG
    c.mi
    cN
    cX
    ngpds.n
    ngpds.x
    ngpds.m
    ngpds.d
    ngpds
    3com23
    eqtrd
end
