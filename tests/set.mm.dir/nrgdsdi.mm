include "cnrg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "cgrp.mm"
include "crg.mm"
include "nrgring.mm"
include "adantr.mm"
include "ringgrp.mm"
include "syl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "nmmul.mm"
include "ringsubdi.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "cngp.mm"
include "nrgngp.mm"
include "ngpds.mm"
include "oveq2d.mm"
include "ringcl.mm"
include "3eqtr4d.mm"

theorem nrgdsdi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cX: class X
  assume nmmul.x: |- X = ( Base ` R )
  assume nmmul.n: |- N = ( norm ` R )
  assume nmmul.t: |- .x. = ( .r ` R )
  assume nrgdsdi.d: |- D = ( dist ` R )


  assert |- ( ( R e. NrmRing /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( N ` A ) x. ( B D C ) ) = ( ( A .x. B ) D ( A .x. C ) ) )

  proof
    cR
    cnrg
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
    cN
    cfv
    #
    cB
    cC
    cR
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cmul
    co
    #
    cA
    cB
    c.x
    co
    #
    cA
    cC
    c.x
    co
    #
    @7
    co
    #
    cN
    cfv
    #
    @6
    cB
    cC
    cD
    co
    #
    cmul
    co
    @11
    @12
    cD
    co
    #
    @5
    cA
    @8
    c.x
    co
    #
    cN
    cfv
    #
    @10
    @14
    @5
    @0
    @1
    @8
    cX
    wcel
    #
    @18
    @10
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    #
    @5
    cR
    cgrp
    wcel
    #
    @2
    @3
    @19
    @5
    cR
    crg
    wcel
    #
    @21
    @0
    @22
    @4
    cR
    nrgring
    adantr
    #
    cR
    ringgrp
    syl
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cX
    cR
    @7
    cB
    cC
    nmmul.x
    @7
    eqid
    #
    grpsubcl
    syl3anc
    cA
    @8
    cR
    c.x
    cN
    cX
    nmmul.x
    nmmul.n
    nmmul.t
    nmmul
    syl3anc
    @5
    @17
    @13
    cN
    @5
    cX
    cR
    c.x
    @7
    cA
    cB
    cC
    nmmul.x
    nmmul.t
    @26
    @23
    @20
    @24
    @25
    ringsubdi
    fveq2d
    eqtr3d
    @5
    @15
    @9
    @6
    cmul
    @5
    cR
    cngp
    wcel
    #
    @2
    @3
    @15
    @9
    wceq
    @0
    @27
    @4
    cR
    nrgngp
    adantr
    #
    @24
    @25
    cB
    cC
    cD
    cR
    @7
    cN
    cX
    nmmul.n
    nmmul.x
    @26
    nrgdsdi.d
    ngpds
    syl3anc
    oveq2d
    @5
    @27
    @11
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    @16
    @14
    wceq
    @28
    @5
    @22
    @1
    @2
    @29
    @23
    @20
    @24
    cX
    cR
    c.x
    cA
    cB
    nmmul.x
    nmmul.t
    ringcl
    syl3anc
    @5
    @22
    @1
    @3
    @30
    @23
    @20
    @25
    cX
    cR
    c.x
    cA
    cC
    nmmul.x
    nmmul.t
    ringcl
    syl3anc
    @11
    @12
    cD
    cR
    @7
    cN
    cX
    nmmul.n
    nmmul.x
    @26
    nrgdsdi.d
    ngpds
    syl3anc
    3eqtr4d
end
