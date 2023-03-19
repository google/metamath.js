include "cnlm.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "csg.mm"
include "cfv.mm"
include "co.mm"
include "cnm.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl.mm"
include "cgrp.mm"
include "cngp.mm"
include "nlmngp2.mm"
include "adantr.mm"
include "ngpgrp.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "nmvs.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmodsubdir.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ngpds.mm"
include "oveq1d.mm"
include "nlmngp.mm"
include "lmodvscl.mm"
include "3eqtr4d.mm"

theorem nlmdsdir
  let cD: class D
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cK: class K
  let cN: class N
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
  assume nlmdsdir.n: |- N = ( norm ` W )
  assume nlmdsdir.e: |- E = ( dist ` F )


  assert |- ( ( W e. NrmMod /\ ( X e. K /\ Y e. K /\ Z e. V ) ) -> ( ( X E Y ) x. ( N ` Z ) ) = ( ( X .x. Z ) D ( Y .x. Z ) ) )

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
    cK
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
    cY
    cF
    csg
    cfv
    #
    co
    #
    cF
    cnm
    cfv
    #
    cfv
    #
    cZ
    cN
    cfv
    #
    cmul
    co
    #
    cX
    cZ
    c.x
    co
    #
    cY
    cZ
    c.x
    co
    #
    cW
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cX
    cY
    cE
    co
    #
    @10
    cmul
    co
    @12
    @13
    cD
    co
    #
    @5
    @7
    cZ
    c.x
    co
    #
    cN
    cfv
    #
    @11
    @16
    @5
    @0
    @7
    cK
    wcel
    #
    @3
    @20
    @11
    wceq
    @0
    @4
    simpl
    @5
    cF
    cgrp
    wcel
    #
    @1
    @2
    @21
    @5
    cF
    cngp
    wcel
    #
    @22
    @0
    @23
    @4
    cF
    cW
    nlmdsdi.f
    nlmngp2
    adantr
    #
    cF
    ngpgrp
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
    cK
    cF
    @6
    cX
    cY
    nlmdsdi.k
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
    @8
    c.x
    cF
    cK
    cN
    cV
    cW
    @7
    cZ
    nlmdsdi.v
    nlmdsdir.n
    nlmdsdi.s
    nlmdsdi.f
    nlmdsdi.k
    @8
    eqid
    #
    nmvs
    syl3anc
    @5
    @19
    @15
    cN
    @5
    cX
    cY
    @6
    c.x
    cF
    cK
    @14
    cV
    cW
    cZ
    nlmdsdi.v
    nlmdsdi.s
    nlmdsdi.f
    nlmdsdi.k
    @14
    eqid
    #
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
    @25
    @26
    @28
    lmodsubdir
    fveq2d
    eqtr3d
    @5
    @17
    @9
    @10
    cmul
    @5
    @23
    @1
    @2
    @17
    @9
    wceq
    @24
    @25
    @26
    cX
    cY
    cE
    cF
    @6
    @8
    cK
    @29
    nlmdsdi.k
    @27
    nlmdsdir.e
    ngpds
    syl3anc
    oveq1d
    @5
    cW
    cngp
    wcel
    #
    @12
    cV
    wcel
    #
    @13
    cV
    wcel
    #
    @18
    @16
    wceq
    @0
    @33
    @4
    cW
    nlmngp
    adantr
    @5
    @31
    @1
    @3
    @34
    @32
    @25
    @28
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
    @5
    @31
    @2
    @3
    @35
    @32
    @26
    @28
    cY
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
    @14
    cN
    cV
    nlmdsdir.n
    nlmdsdi.v
    @30
    nlmdsdi.d
    ngpds
    syl3anc
    3eqtr4d
end
