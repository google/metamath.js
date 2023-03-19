include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cabl.mm"
include "cmgp.mm"
include "cfv.mm"
include "csgrp.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "wral.mm"
include "w3a.mm"
include "crng.mm"
include "ccrg.mm"
include "wi.mm"
include "cn0.mm"
include "nnnn0.mm"
include "zncrng.mm"
include "syl.mm"
include "crg.mm"
include "crngring.mm"
include "ring0cl.mm"
include "eleq1a.mm"
include "imp.mm"
include "cznabel.mm"
include "adantlr.mm"
include "eqid.mm"
include "cznrnglem.mm"
include "mgpbas.mm"
include "cnx.mm"
include "cmulr.mm"
include "cop.mm"
include "csts.mm"
include "fveq2i.mm"
include "cvv.mm"
include "czn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cbs.mm"
include "mpt2ex.mm"
include "mulrid.mm"
include "setsid.mm"
include "mp2an.mm"
include "mgpplusg.mm"
include "eqcomi.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "adantl.mm"
include "simpr.mm"
include "copissgrp.mm"
include "oveq1.mm"
include "ad3antlr.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "adantr.mm"
include "anim1i.mm"
include "mndlid.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "weq.mm"
include "simpr1.mm"
include "simpr2.mm"
include "ovmpt2d.mm"
include "simpr3.mm"
include "oveq12d.mm"
include "ad3antrrr.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "3eqtr4rd.mm"
include "jca.mm"
include "ralrimivvva.mm"
include "3jca.mm"
include "mpdan.mm"
include "plusgid.mm"
include "plusgndxnmulrndx.mm"
include "setsnid.mm"
include "eqtr4i.mm"
include "eqtri.mm"
include "isrng.mm"
include "sylibr.mm"

theorem cznrng
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume cznrng.y: |- Y = ( Z/nZ ` N )
  assume cznrng.b: |- B = ( Base ` Y )
  assume cznrng.x: |- X = ( Y sSet <. ( .r ` ndx ) , ( x e. B , y e. B |-> C ) >. )
  assume cznrng.0: |- .0. = ( 0g ` Y )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint Y x
  disjoint Y y
  disjoint .0. x
  disjoint .0. y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint .0. a
  disjoint .0. b
  disjoint .0. c
  disjoint k x
  assert |- ( ( N e. NN /\ C = .0. ) -> X e. Rng )

  proof
    cN
    cn
    wcel
    #
    cC
    c.0
    wceq
    #
    wa
    #
    cX
    cabl
    wcel
    #
    cX
    cmgp
    cfv
    #
    csgrp
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    vx
    vy
    cB
    cB
    cC
    cmpt2
    #
    co
    #
    @6
    @7
    @11
    co
    #
    @6
    @8
    @11
    co
    #
    @9
    co
    #
    wceq
    #
    @6
    @7
    @9
    co
    #
    @8
    @11
    co
    #
    @14
    @7
    @8
    @11
    co
    #
    @9
    co
    #
    wceq
    #
    wa
    #
    vc
    cB
    wral
    vb
    cB
    wral
    va
    cB
    wral
    #
    w3a
    #
    cX
    crng
    wcel
    @2
    cC
    cB
    wcel
    #
    @24
    @0
    @1
    @25
    @0
    cY
    ccrg
    wcel
    #
    @1
    @25
    wi
    #
    @0
    cN
    cn0
    wcel
    @26
    cN
    nnnn0
    cN
    cY
    cznrng.y
    zncrng
    syl
    #
    @26
    cY
    crg
    wcel
    #
    @27
    cY
    crngring
    #
    @29
    c.0
    cB
    wcel
    @27
    cB
    cY
    c.0
    cznrng.b
    cznrng.0
    ring0cl
    c.0
    cB
    cC
    eleq1a
    syl
    syl
    syl
    imp
    @2
    @25
    wa
    #
    @3
    @5
    @23
    @0
    @25
    @3
    @1
    vx
    vy
    cB
    cC
    cN
    cX
    cY
    cznrng.y
    cznrng.b
    cznrng.x
    cznabel
    adantlr
    @31
    vx
    vy
    cB
    cC
    @4
    cB
    cX
    @4
    @4
    eqid
    #
    vx
    vy
    cB
    cC
    cN
    cX
    cY
    cznrng.y
    cznrng.b
    cznrng.x
    cznrnglem
    #
    mgpbas
    @11
    @4
    cplusg
    cfv
    cY
    cnx
    cmulr
    cfv
    #
    @11
    cop
    csts
    co
    #
    @11
    @4
    cX
    @35
    cmgp
    cznrng.x
    fveq2i
    cY
    cvv
    wcel
    @11
    cvv
    wcel
    @11
    @35
    cmulr
    cfv
    #
    wceq
    cY
    cN
    czn
    cfv
    cvv
    cznrng.y
    cN
    czn
    fvex
    eqeltri
    vx
    vy
    cB
    cB
    cC
    cB
    cY
    cbs
    cfv
    cvv
    cznrng.b
    cY
    cbs
    fvex
    eqeltri
    #
    @37
    mpt2ex
    cvv
    @11
    cmulr
    cvv
    cY
    mulrid
    setsid
    mp2an
    #
    mgpplusg
    eqcomi
    @25
    cB
    c0
    wne
    @2
    cB
    cC
    ne0i
    adantl
    @2
    @25
    simpr
    #
    copissgrp
    @31
    @22
    va
    vb
    vc
    cB
    cB
    cB
    @31
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    w3a
    #
    wa
    #
    @16
    @21
    @44
    cC
    cC
    @9
    co
    #
    cC
    @15
    @12
    @44
    @45
    c.0
    cC
    @9
    co
    #
    cC
    @1
    @45
    @46
    wceq
    @0
    @25
    @43
    cC
    c.0
    cC
    @9
    oveq1
    ad3antlr
    @44
    cY
    cmnd
    wcel
    #
    @25
    wa
    #
    @46
    cC
    wceq
    @31
    @48
    @43
    @2
    @47
    @25
    @0
    @47
    @1
    @0
    @29
    @47
    @0
    @26
    @29
    @28
    @30
    syl
    #
    cY
    ringmnd
    syl
    adantr
    anim1i
    adantr
    cB
    @9
    cY
    cC
    c.0
    cznrng.b
    @9
    eqid
    #
    cznrng.0
    mndlid
    syl
    eqtrd
    #
    @44
    @13
    cC
    @14
    cC
    @9
    @44
    vx
    vy
    @6
    @7
    cB
    cB
    cC
    cC
    @11
    cB
    @44
    @11
    eqidd
    #
    @44
    vx
    va
    weq
    #
    vy
    vb
    weq
    wa
    wa
    cC
    eqidd
    @31
    @40
    @41
    @42
    simpr1
    #
    @31
    @40
    @41
    @42
    simpr2
    #
    @31
    @25
    @43
    @39
    adantr
    #
    ovmpt2d
    @44
    vx
    vy
    @6
    @8
    cB
    cB
    cC
    cC
    @11
    cB
    @52
    @44
    @53
    vy
    vc
    weq
    #
    wa
    wa
    cC
    eqidd
    @54
    @31
    @40
    @41
    @42
    simpr3
    #
    @56
    ovmpt2d
    #
    oveq12d
    @44
    vx
    vy
    @6
    @10
    cB
    cB
    cC
    cC
    @11
    cB
    @52
    @44
    @53
    vy
    cv
    @10
    wceq
    wa
    wa
    cC
    eqidd
    @54
    @44
    @29
    @41
    @42
    @10
    cB
    wcel
    @0
    @29
    @1
    @25
    @43
    @49
    ad3antrrr
    #
    @55
    @58
    cB
    @9
    cY
    @7
    @8
    cznrng.b
    @50
    ringacl
    syl3anc
    @56
    ovmpt2d
    3eqtr4rd
    @44
    @45
    cC
    @20
    @18
    @51
    @44
    @14
    cC
    @19
    cC
    @9
    @59
    @44
    vx
    vy
    @7
    @8
    cB
    cB
    cC
    cC
    @11
    cB
    @52
    @44
    vx
    vb
    weq
    @57
    wa
    wa
    cC
    eqidd
    @55
    @58
    @56
    ovmpt2d
    oveq12d
    @44
    vx
    vy
    @17
    @8
    cB
    cB
    cC
    cC
    @11
    cB
    @52
    @44
    vx
    cv
    @17
    wceq
    @57
    wa
    wa
    cC
    eqidd
    @44
    @29
    @40
    @41
    @17
    cB
    wcel
    @60
    @54
    @55
    cB
    @9
    cY
    @6
    @7
    cznrng.b
    @50
    ringacl
    syl3anc
    @58
    @56
    ovmpt2d
    3eqtr4rd
    jca
    ralrimivvva
    3jca
    mpdan
    va
    vb
    vc
    cB
    @9
    cX
    @11
    @4
    @33
    @32
    @9
    @35
    cplusg
    cfv
    cX
    cplusg
    cfv
    @11
    @34
    cplusg
    cY
    plusgid
    plusgndxnmulrndx
    setsnid
    cX
    @35
    cplusg
    cznrng.x
    fveq2i
    eqtr4i
    @11
    @36
    cX
    cmulr
    cfv
    @38
    @35
    cX
    cmulr
    cX
    @35
    cznrng.x
    eqcomi
    fveq2i
    eqtri
    isrng
    sylibr
end
