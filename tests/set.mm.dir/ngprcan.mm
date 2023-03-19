include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "csg.mm"
include "cfv.mm"
include "cnm.mm"
include "cgrp.mm"
include "wceq.mm"
include "ngpgrp.mm"
include "eqid.mm"
include "grppnpcan2.mm"
include "sylan.mm"
include "fveq2d.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simpr2.mm"
include "ngpds.mm"
include "3eqtr4d.mm"

theorem ngprcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cG: class G
  let cX: class X
  assume ngprcan.x: |- X = ( Base ` G )
  assume ngprcan.p: |- .+ = ( +g ` G )
  assume ngprcan.d: |- D = ( dist ` G )


  assert |- ( ( G e. NrmGrp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A .+ C ) D ( B .+ C ) ) = ( A D B ) )

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
    c.pl
    co
    #
    cB
    cC
    c.pl
    co
    #
    cG
    csg
    cfv
    #
    co
    #
    cG
    cnm
    cfv
    #
    cfv
    #
    cA
    cB
    @8
    co
    #
    @10
    cfv
    #
    @6
    @7
    cD
    co
    #
    cA
    cB
    cD
    co
    #
    @5
    @9
    @12
    @10
    @0
    cG
    cgrp
    wcel
    #
    @4
    @9
    @12
    wceq
    cG
    ngpgrp
    #
    cX
    c.pl
    cG
    @8
    cA
    cB
    cC
    ngprcan.x
    ngprcan.p
    @8
    eqid
    #
    grppnpcan2
    sylan
    fveq2d
    @5
    @0
    @6
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    @14
    @11
    wceq
    @0
    @4
    simpl
    #
    @5
    @16
    @1
    @3
    @19
    @0
    @16
    @4
    @17
    adantr
    #
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
    c.pl
    cG
    cA
    cC
    ngprcan.x
    ngprcan.p
    grpcl
    syl3anc
    @5
    @16
    @2
    @3
    @20
    @22
    @0
    @1
    @2
    @3
    simpr2
    #
    @24
    cX
    c.pl
    cG
    cB
    cC
    ngprcan.x
    ngprcan.p
    grpcl
    syl3anc
    @6
    @7
    cD
    cG
    @8
    @10
    cX
    @10
    eqid
    #
    ngprcan.x
    @18
    ngprcan.d
    ngpds
    syl3anc
    @5
    @0
    @1
    @2
    @15
    @13
    wceq
    @21
    @23
    @25
    cA
    cB
    cD
    cG
    @8
    @10
    cX
    @26
    ngprcan.x
    @18
    ngprcan.d
    ngpds
    syl3anc
    3eqtr4d
end
