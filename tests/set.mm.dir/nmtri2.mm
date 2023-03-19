include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "cgrp.mm"
include "wceq.mm"
include "ngpgrp.mm"
include "eqid.mm"
include "grpnpncan.mm"
include "eqcomd.mm"
include "sylan.mm"
include "fveq2d.mm"
include "wbr.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "nmtri.mm"
include "eqbrtrd.mm"

theorem nmtri2
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume nmtri2.x: |- X = ( Base ` G )
  assume nmtri2.n: |- N = ( norm ` G )
  assume nmtri2.m: |- .- = ( -g ` G )


  assert |- ( ( G e. NrmGrp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( N ` ( A .- C ) ) <_ ( ( N ` ( A .- B ) ) + ( N ` ( B .- C ) ) ) )

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
    cN
    cfv
    cA
    cB
    c.mi
    co
    #
    cB
    cC
    c.mi
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cN
    cfv
    #
    @7
    cN
    cfv
    @8
    cN
    cfv
    caddc
    co
    #
    cle
    @5
    @6
    @10
    cN
    @0
    cG
    cgrp
    wcel
    #
    @4
    @6
    @10
    wceq
    cG
    ngpgrp
    #
    @13
    @4
    wa
    @10
    @6
    cX
    @9
    cG
    c.mi
    cA
    cB
    cC
    nmtri2.x
    @9
    eqid
    #
    nmtri2.m
    grpnpncan
    eqcomd
    sylan
    fveq2d
    @5
    @0
    @7
    cX
    wcel
    #
    @8
    cX
    wcel
    #
    @11
    @12
    cle
    wbr
    @0
    @4
    simpl
    @5
    @13
    @1
    @2
    @16
    @0
    @13
    @4
    @14
    adantr
    #
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    #
    cX
    cG
    c.mi
    cA
    cB
    nmtri2.x
    nmtri2.m
    grpsubcl
    syl3anc
    @5
    @13
    @2
    @3
    @17
    @18
    @19
    @0
    @1
    @2
    @3
    simpr3
    cX
    cG
    c.mi
    cB
    cC
    nmtri2.x
    nmtri2.m
    grpsubcl
    syl3anc
    @7
    @8
    @9
    cG
    cN
    cX
    nmtri2.x
    nmtri2.n
    @15
    nmtri
    syl3anc
    eqbrtrd
end
