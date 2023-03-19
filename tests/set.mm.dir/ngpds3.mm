include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "ngpds2.mm"
include "cxme.mm"
include "wceq.mm"
include "ngpxms.mm"
include "3ad2ant1.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpsubcl.mm"
include "syl3an1.mm"
include "grpidcl.mm"
include "syl.mm"
include "xmssym.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem ngpds3
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


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( A D B ) = ( .0. D ( A .- B ) ) )

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
    #
    cA
    cB
    cD
    co
    cA
    cB
    c.mi
    co
    #
    c.0
    cD
    co
    #
    c.0
    @4
    cD
    co
    #
    cA
    cB
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
    @3
    cG
    cxme
    wcel
    #
    @4
    cX
    wcel
    #
    c.0
    cX
    wcel
    #
    @5
    @6
    wceq
    @0
    @1
    @7
    @2
    cG
    ngpxms
    3ad2ant1
    @0
    cG
    cgrp
    wcel
    #
    @1
    @2
    @8
    cG
    ngpgrp
    #
    cX
    cG
    c.mi
    cA
    cB
    ngpds2.x
    ngpds2.m
    grpsubcl
    syl3an1
    @3
    @10
    @9
    @0
    @1
    @10
    @2
    @11
    3ad2ant1
    cX
    cG
    c.0
    ngpds2.x
    ngpds2.z
    grpidcl
    syl
    @4
    c.0
    cD
    cG
    cX
    ngpds2.x
    ngpds2.d
    xmssym
    syl3anc
    eqtrd
end
