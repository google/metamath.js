include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cnm.mm"
include "cfv.mm"
include "eqid.mm"
include "ngpds.mm"
include "wceq.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpsubcl.mm"
include "syl3an1.mm"
include "nmval.mm"
include "syl.mm"
include "eqtrd.mm"

theorem ngpds2
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


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( A D B ) = ( ( A .- B ) D .0. ) )

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
    cG
    cnm
    cfv
    #
    cfv
    #
    @4
    c.0
    cD
    co
    #
    cA
    cB
    cD
    cG
    c.mi
    @5
    cX
    @5
    eqid
    #
    ngpds2.x
    ngpds2.m
    ngpds2.d
    ngpds
    @3
    @4
    cX
    wcel
    #
    @6
    @7
    wceq
    @0
    cG
    cgrp
    wcel
    @1
    @2
    @9
    cG
    ngpgrp
    cX
    cG
    c.mi
    cA
    cB
    ngpds2.x
    ngpds2.m
    grpsubcl
    syl3an1
    @4
    cD
    @5
    cG
    cX
    c.0
    @8
    ngpds2.x
    ngpds2.z
    ngpds2.d
    nmval
    syl
    eqtrd
end
