include "cnlm.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "cnm.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "cgrp.mm"
include "cngp.mm"
include "nlmngp.mm"
include "adantr.mm"
include "ngpgrp.mm"
include "syl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "nmvs.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmodsubdi.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ngpds.mm"
include "oveq2d.mm"
include "lmodvscl.mm"
include "3eqtr4d.mm"

theorem nlmdsdi
  let cA: class A
  let cD: class D
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume nlmdsdi.v: |- V = ( Base ` W )
  assume nlmdsdi.s: |- .x. = ( .s ` W )
  assume nlmdsdi.f: |- F = ( Scalar ` W )
  assume nlmdsdi.k: |- K = ( Base ` F )
  assume nlmdsdi.d: |- D = ( dist ` W )
  assume nlmdsdi.a: |- A = ( norm ` F )


  assert |- ( ( W e. NrmMod /\ ( X e. K /\ Y e. V /\ Z e. V ) ) -> ( ( A ` X ) x. ( Y D Z ) ) = ( ( X .x. Y ) D ( X .x. Z ) ) )

  proof
    cW
    cnlm
    wcel
    #
    cX
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    cZ
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cA
    cfv
    #
    cY
    cZ
    cW
    csg
    cfv
    #
    co
    #
    cW
    cnm
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cX
    cY
    c.x
    co
    #
    cX
    cZ
    c.x
    co
    #
    @7
    co
    #
    @9
    cfv
    #
    @6
    cY
    cZ
    cD
    co
    #
    cmul
    co
    @12
    @13
    cD
    co
    #
    @5
    cX
    @8
    c.x
    co
    #
    @9
    cfv
    #
    @11
    @15
    @5
    @0
    @1
    @8
    cV
    wcel
    #
    @19
    @11
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
    cW
    cgrp
    wcel
    #
    @2
    @3
    @20
    @5
    cW
    cngp
    wcel
    #
    @22
    @0
    @23
    @4
    cW
    nlmngp
    adantr
    #
    cW
    ngpgrp
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
    cV
    cW
    @7
    cY
    cZ
    nlmdsdi.v
    @7
    eqid
    #
    grpsubcl
    syl3anc
    cA
    c.x
    cF
    cK
    @9
    cV
    cW
    cX
    @8
    nlmdsdi.v
    @9
    eqid
    #
    nlmdsdi.s
    nlmdsdi.f
    nlmdsdi.k
    nlmdsdi.a
    nmvs
    syl3anc
    @5
    @18
    @14
    @9
    @5
    cX
    c.x
    cF
    cK
    @7
    cV
    cW
    cY
    cZ
    nlmdsdi.v
    nlmdsdi.s
    nlmdsdi.f
    nlmdsdi.k
    @27
    @0
    cW
    clmod
    wcel
    #
    @4
    cW
    nlmlmod
    adantr
    #
    @21
    @25
    @26
    lmodsubdi
    fveq2d
    eqtr3d
    @5
    @16
    @10
    @6
    cmul
    @5
    @23
    @2
    @3
    @16
    @10
    wceq
    @24
    @25
    @26
    cY
    cZ
    cD
    cW
    @7
    @9
    cV
    @28
    nlmdsdi.v
    @27
    nlmdsdi.d
    ngpds
    syl3anc
    oveq2d
    @5
    @23
    @12
    cV
    wcel
    #
    @13
    cV
    wcel
    #
    @17
    @15
    wceq
    @24
    @5
    @29
    @1
    @2
    @31
    @30
    @21
    @25
    cX
    c.x
    cF
    cK
    cV
    cW
    cY
    nlmdsdi.v
    nlmdsdi.f
    nlmdsdi.s
    nlmdsdi.k
    lmodvscl
    syl3anc
    @5
    @29
    @1
    @3
    @32
    @30
    @21
    @26
    cX
    c.x
    cF
    cK
    cV
    cW
    cZ
    nlmdsdi.v
    nlmdsdi.f
    nlmdsdi.s
    nlmdsdi.k
    lmodvscl
    syl3anc
    @12
    @13
    cD
    cW
    @7
    @9
    cV
    @28
    nlmdsdi.v
    @27
    nlmdsdi.d
    ngpds
    syl3anc
    3eqtr4d
end
