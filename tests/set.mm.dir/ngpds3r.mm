include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cxme.mm"
include "wceq.mm"
include "ngpxms.mm"
include "xmssym.mm"
include "syl3an1.mm"
include "ngpds3.mm"
include "3com23.mm"
include "eqtrd.mm"

theorem ngpds3r
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


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( A D B ) = ( .0. D ( B .- A ) ) )

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
    c.0
    cB
    cA
    c.mi
    co
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
    ngpds3
    3com23
    eqtrd
end
