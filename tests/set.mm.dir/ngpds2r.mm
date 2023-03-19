include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cxme.mm"
include "wceq.mm"
include "ngpxms.mm"
include "xmssym.mm"
include "syl3an1.mm"
include "ngpds2.mm"
include "3com23.mm"
include "eqtrd.mm"

theorem ngpds2r
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let c.0: class .0.
  assume ngpds2.x: |- X = ( Base ` G )
  assume ngpds2.z: |- .0. = ( 0g ` G )
  assume ngpds2.m: |- .- = ( -g ` G )
  assume ngpds2.d: |- D = ( dist ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( A D B ) = ( ( B .- A ) D .0. ) )

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
    c.0
    cD
    co
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
    ngpds2.x
    ngpds2.d
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
    cX
    c.0
    ngpds2.x
    ngpds2.z
    ngpds2.m
    ngpds2.d
    ngpds2
    3com23
    eqtrd
end
