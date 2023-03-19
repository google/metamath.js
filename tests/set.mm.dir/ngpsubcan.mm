include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "simpr1.mm"
include "simpr3.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "oveq12d.mm"
include "simpl.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "adantr.mm"
include "grpinvcl.mm"
include "ngprcan.mm"
include "syl13anc.mm"
include "eqtrd.mm"

theorem ngpsubcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let c.mi: class .-
  let cX: class X
  assume ngpsubcan.x: |- X = ( Base ` G )
  assume ngpsubcan.m: |- .- = ( -g ` G )
  assume ngpsubcan.d: |- D = ( dist ` G )


  assert |- ( ( G e. NrmGrp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A .- C ) D ( B .- C ) ) = ( A D B ) )

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
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cC
    c.mi
    co
    #
    cB
    cC
    c.mi
    co
    #
    cD
    co
    cA
    cC
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cB
    @9
    @10
    co
    #
    cD
    co
    #
    cA
    cB
    cD
    co
    #
    @5
    @6
    @11
    @7
    @12
    cD
    @5
    @1
    @3
    @6
    @11
    wceq
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cX
    @10
    cG
    @8
    c.mi
    cA
    cC
    ngpsubcan.x
    @10
    eqid
    #
    @8
    eqid
    #
    ngpsubcan.m
    grpsubval
    syl2anc
    @5
    @2
    @3
    @7
    @12
    wceq
    @0
    @1
    @2
    @3
    simpr2
    #
    @16
    cX
    @10
    cG
    @8
    c.mi
    cB
    cC
    ngpsubcan.x
    @17
    @18
    ngpsubcan.m
    grpsubval
    syl2anc
    oveq12d
    @5
    @0
    @1
    @2
    @9
    cX
    wcel
    #
    @13
    @14
    wceq
    @0
    @4
    simpl
    @15
    @19
    @5
    cG
    cgrp
    wcel
    #
    @3
    @20
    @0
    @21
    @4
    cG
    ngpgrp
    adantr
    @16
    cX
    cG
    @8
    cC
    ngpsubcan.x
    @18
    grpinvcl
    syl2anc
    cA
    cB
    @9
    cD
    @10
    cG
    cX
    ngpsubcan.x
    @17
    ngpsubcan.d
    ngprcan
    syl13anc
    eqtrd
end
