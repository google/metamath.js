include "cnrg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "csg.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl.mm"
include "cgrp.mm"
include "crg.mm"
include "nrgring.mm"
include "adantr.mm"
include "ringgrp.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "nmmul.mm"
include "rngsubdir.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "cngp.mm"
include "nrgngp.mm"
include "ngpds.mm"
include "oveq1d.mm"
include "ringcl.mm"
include "3eqtr4d.mm"

theorem nrgdsdir
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


  assert |- ( ( R e. NrmRing /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D B ) x. ( N ` C ) ) = ( ( A .x. C ) D ( B .x. C ) ) )

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
    cB
    cR
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cC
    cN
    cfv
    #
    cmul
    co
    #
    cA
    cC
    c.x
    co
    #
    cB
    cC
    c.x
    co
    #
    @6
    co
    #
    cN
    cfv
    #
    cA
    cB
    cD
    co
    #
    @9
    cmul
    co
    @11
    @12
    cD
    co
    #
    @5
    @7
    cC
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
    @7
    cX
    wcel
    #
    @3
    @18
    @10
    wceq
    @0
    @4
    simpl
    @5
    cR
    cgrp
    wcel
    #
    @1
    @2
    @19
    @5
    cR
    crg
    wcel
    #
    @20
    @0
    @21
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
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    cX
    cR
    @6
    cA
    cB
    nmmul.x
    @6
    eqid
    #
    grpsubcl
    syl3anc
    @0
    @1
    @2
    @3
    simpr3
    #
    @7
    cC
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
    @6
    cA
    cB
    cC
    nmmul.x
    nmmul.t
    @25
    @22
    @23
    @24
    @26
    rngsubdir
    fveq2d
    eqtr3d
    @5
    @15
    @8
    @9
    cmul
    @5
    cR
    cngp
    wcel
    #
    @1
    @2
    @15
    @8
    wceq
    @0
    @27
    @4
    cR
    nrgngp
    adantr
    #
    @23
    @24
    cA
    cB
    cD
    cR
    @6
    cN
    cX
    nmmul.n
    nmmul.x
    @25
    nrgdsdi.d
    ngpds
    syl3anc
    oveq1d
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
    @21
    @1
    @3
    @29
    @22
    @23
    @26
    cX
    cR
    c.x
    cA
    cC
    nmmul.x
    nmmul.t
    ringcl
    syl3anc
    @5
    @21
    @2
    @3
    @30
    @22
    @24
    @26
    cX
    cR
    c.x
    cB
    cC
    nmmul.x
    nmmul.t
    ringcl
    syl3anc
    @11
    @12
    cD
    cR
    @6
    cN
    cX
    nmmul.n
    nmmul.x
    @25
    nrgdsdi.d
    ngpds
    syl3anc
    3eqtr4d
end
