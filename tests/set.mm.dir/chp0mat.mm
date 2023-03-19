include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cascl.mm"
include "csg.mm"
include "cmpt.mm"
include "cgsu.mm"
include "chash.mm"
include "cbs.mm"
include "wne.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "simpl.mm"
include "simpr.mm"
include "crg.mm"
include "cgrp.mm"
include "crngring.mm"
include "matring.mm"
include "sylan2.mm"
include "ringgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "3syl.mm"
include "cvv.mm"
include "cmpt2.mm"
include "mat0op.mm"
include "syl5eq.mm"
include "adantr.mm"
include "weq.mm"
include "eqidd.mm"
include "adantl.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "a1d.mm"
include "ralrimivva.mm"
include "chpdmat.mm"
include "syl31anc.mm"
include "fveq2d.mm"
include "ply1scl0.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ply1ring.mm"
include "vr1cl.mm"
include "jca.mm"
include "grpsubid1.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ccmn.mm"
include "ply1crng.mm"
include "crngmgp.mm"
include "cmnmnd.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "gsumconst.mm"
include "syl3anc.mm"
include "3eqtrd.mm"

theorem chp0mat
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume chp0mat.c: |- C = ( N CharPlyMat R )
  assume chp0mat.p: |- P = ( Poly1 ` R )
  assume chp0mat.a: |- A = ( N Mat R )
  assume chp0mat.x: |- X = ( var1 ` R )
  assume chp0mat.g: |- G = ( mulGrp ` P )
  assume chp0mat.m: |- .^ = ( .g ` G )
  assume chp0mat.0: |- .0. = ( 0g ` A )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> ( C ` .0. ) = ( ( # ` N ) .^ X ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    c.0
    cC
    cfv
    #
    cG
    vk
    cN
    cX
    vk
    cv
    #
    @4
    c.0
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cP
    csg
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    cN
    cX
    cmpt
    #
    cgsu
    co
    #
    cN
    chash
    cfv
    cX
    c.ex
    co
    #
    @2
    @0
    @1
    c.0
    cA
    cbs
    cfv
    #
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @17
    @18
    c.0
    co
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @3
    @11
    wceq
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    @2
    cA
    crg
    wcel
    #
    cA
    cgrp
    wcel
    @16
    @1
    @0
    cR
    crg
    wcel
    #
    @24
    cR
    crngring
    #
    cA
    cR
    cN
    chp0mat.a
    matring
    sylan2
    cA
    ringgrp
    @15
    cA
    c.0
    @15
    eqid
    #
    chp0mat.0
    grpidcl
    3syl
    @2
    @22
    vi
    vj
    cN
    cN
    @2
    @17
    cN
    wcel
    #
    @18
    cN
    wcel
    #
    wa
    #
    wa
    #
    @21
    @19
    @31
    vx
    vy
    @17
    @18
    cN
    cN
    @20
    @20
    c.0
    cvv
    @2
    c.0
    vx
    vy
    cN
    cN
    @20
    cmpt2
    #
    wceq
    #
    @30
    @1
    @0
    @25
    @33
    @26
    @0
    @25
    wa
    c.0
    cA
    c0g
    cfv
    @32
    chp0mat.0
    cA
    cR
    vx
    vy
    cN
    @20
    chp0mat.a
    @20
    eqid
    #
    mat0op
    syl5eq
    sylan2
    #
    adantr
    @31
    vx
    vi
    weq
    vy
    vj
    weq
    wa
    wa
    @20
    eqidd
    @30
    @28
    @2
    @28
    @29
    simpl
    adantl
    @30
    @29
    @2
    @28
    @29
    simpr
    adantl
    @31
    cR
    c0g
    fvexd
    ovmpt2d
    a1d
    ralrimivva
    cA
    @15
    cC
    cP
    cR
    @6
    vi
    vj
    vk
    cG
    c.0
    @8
    cN
    cX
    @20
    chp0mat.c
    chp0mat.p
    chp0mat.a
    @6
    eqid
    #
    @27
    chp0mat.x
    @34
    chp0mat.g
    @8
    eqid
    #
    chpdmat
    syl31anc
    @2
    @10
    @12
    cG
    cgsu
    @2
    vk
    cN
    @9
    cX
    @2
    @4
    cN
    wcel
    #
    wa
    #
    @9
    cX
    cP
    c0g
    cfv
    #
    @8
    co
    #
    cX
    @39
    @7
    @40
    cX
    @8
    @39
    @7
    @20
    @6
    cfv
    #
    @40
    @39
    @5
    @20
    @6
    @39
    vx
    vy
    @4
    @4
    cN
    cN
    @20
    @20
    c.0
    cvv
    @2
    @33
    @38
    @35
    adantr
    @39
    vx
    vk
    weq
    vy
    vk
    weq
    wa
    wa
    @20
    eqidd
    @2
    @38
    simpr
    #
    @43
    @39
    cR
    c0g
    fvexd
    ovmpt2d
    fveq2d
    @2
    @42
    @40
    wceq
    #
    @38
    @2
    @25
    @44
    @1
    @25
    @0
    @26
    adantl
    #
    @6
    cP
    cR
    @40
    @20
    chp0mat.p
    @36
    @34
    @40
    eqid
    #
    ply1scl0
    syl
    adantr
    eqtrd
    oveq2d
    @39
    cP
    cgrp
    wcel
    #
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @41
    cX
    wceq
    @2
    @50
    @38
    @2
    @47
    @49
    @1
    @47
    @0
    @1
    @25
    cP
    crg
    wcel
    @47
    @26
    cP
    cR
    chp0mat.p
    ply1ring
    cP
    ringgrp
    3syl
    adantl
    @2
    @25
    @49
    @45
    @48
    cP
    cR
    cX
    chp0mat.x
    chp0mat.p
    @48
    eqid
    #
    vr1cl
    #
    syl
    jca
    adantr
    @48
    cP
    @8
    cX
    @40
    @51
    @46
    @37
    grpsubid1
    syl
    eqtrd
    mpteq2dva
    oveq2d
    @2
    cG
    cmnd
    wcel
    #
    @0
    cX
    cG
    cbs
    cfv
    #
    wcel
    @13
    @14
    wceq
    @1
    @53
    @0
    @1
    cP
    ccrg
    wcel
    cG
    ccmn
    wcel
    @53
    cP
    cR
    chp0mat.p
    ply1crng
    cP
    cG
    chp0mat.g
    crngmgp
    cG
    cmnmnd
    3syl
    adantl
    @23
    @2
    cX
    @48
    @54
    @1
    @49
    @0
    @1
    @25
    @49
    @26
    @52
    syl
    adantl
    @48
    cP
    cG
    chp0mat.g
    @51
    mgpbas
    syl6eleq
    cN
    @54
    c.ex
    vk
    cG
    cX
    @54
    eqid
    chp0mat.m
    gsumconst
    syl3anc
    3eqtrd
end
