include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
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
include "crngring.mm"
include "matring.mm"
include "sylan2.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "weq.mm"
include "cif.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "simplrl.mm"
include "simplrr.mm"
include "mat1ov.mm"
include "ifnefalse.mm"
include "eqtrd.mm"
include "ex.mm"
include "ralrimivva.mm"
include "chpdmat.mm"
include "syl31anc.mm"
include "adantr.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ccmn.mm"
include "ply1crng.mm"
include "crngmgp.mm"
include "cmnmnd.mm"
include "3syl.mm"
include "cgrp.mm"
include "w3a.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "vr1cl.mm"
include "cur.mm"
include "ply1scl1.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "grpsubcl.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "gsumconst.mm"
include "eqcomi.mm"
include "oveqi.mm"
include "oveq2i.mm"
include "syl3anc.mm"

theorem chpidmat
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let c.mi: class .-
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
  assume chpidmat.i: |- I = ( 1r ` A )
  assume chpidmat.s: |- S = ( algSc ` P )
  assume chpidmat.1: |- .1. = ( 1r ` R )
  assume chpidmat.m: |- .- = ( -g ` P )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> ( C ` I ) = ( ( # ` N ) .^ ( X .- ( S ` .1. ) ) ) )

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
    cI
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
    cI
    co
    #
    cS
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
    cN
    chash
    cfv
    #
    cX
    c.1
    cS
    cfv
    #
    c.mi
    co
    #
    c.ex
    co
    #
    @2
    @0
    @1
    cI
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
    cI
    co
    #
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
    @10
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
    @16
    @1
    @0
    cR
    crg
    wcel
    #
    @25
    cR
    crngring
    #
    cA
    cR
    cN
    chp0mat.a
    matring
    sylan2
    @15
    cA
    cI
    @15
    eqid
    #
    chpidmat.i
    ringidcl
    syl
    @2
    @23
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
    @19
    @22
    @32
    @19
    wa
    #
    @20
    vi
    vj
    weq
    c.1
    @21
    cif
    #
    @21
    @33
    cA
    cR
    cI
    c.1
    @17
    @18
    cN
    @21
    chp0mat.a
    chpidmat.1
    @21
    eqid
    #
    @2
    @0
    @31
    @19
    @24
    ad2antrr
    @2
    @26
    @31
    @19
    @1
    @26
    @0
    @27
    adantl
    #
    ad2antrr
    @2
    @29
    @30
    @19
    simplrl
    @2
    @29
    @30
    @19
    simplrr
    chpidmat.i
    mat1ov
    @19
    @34
    @21
    wceq
    @32
    @17
    @18
    c.1
    @21
    ifnefalse
    adantl
    eqtrd
    ex
    ralrimivva
    cA
    @15
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    cG
    cI
    @7
    cN
    cX
    @21
    chp0mat.c
    chp0mat.p
    chp0mat.a
    chpidmat.s
    @28
    chp0mat.x
    @35
    chp0mat.g
    @7
    eqid
    #
    chpdmat
    syl31anc
    @2
    @10
    cG
    vk
    cN
    cX
    @12
    @7
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @14
    @2
    @9
    @39
    cG
    cgsu
    @2
    vk
    cN
    @8
    @38
    @2
    @4
    cN
    wcel
    #
    wa
    #
    @6
    @12
    cX
    @7
    @42
    @5
    c.1
    cS
    @42
    @5
    vk
    vk
    weq
    #
    c.1
    @21
    cif
    c.1
    @42
    cA
    cR
    cI
    c.1
    @4
    @4
    cN
    @21
    chp0mat.a
    chpidmat.1
    @35
    @2
    @0
    @41
    @24
    adantr
    @2
    @26
    @41
    @36
    adantr
    @2
    @41
    simpr
    #
    @44
    chpidmat.i
    mat1ov
    @43
    c.1
    @21
    @4
    eqid
    iftruei
    syl6eq
    fveq2d
    oveq2d
    mpteq2dva
    oveq2d
    @2
    cG
    cmnd
    wcel
    #
    @0
    @38
    cG
    cbs
    cfv
    #
    wcel
    #
    @40
    @14
    wceq
    @1
    @45
    @0
    @1
    cP
    ccrg
    wcel
    cG
    ccmn
    wcel
    @45
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
    @24
    @2
    @38
    cP
    cbs
    cfv
    #
    @46
    @2
    cP
    cgrp
    wcel
    #
    cX
    @48
    wcel
    #
    @12
    @48
    wcel
    #
    w3a
    #
    @38
    @48
    wcel
    @1
    @52
    @0
    @1
    @26
    @52
    @27
    @26
    @49
    @50
    @51
    @26
    cP
    crg
    wcel
    #
    @49
    cP
    cR
    chp0mat.p
    ply1ring
    #
    cP
    ringgrp
    syl
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
    @26
    @12
    cP
    cur
    cfv
    #
    @48
    cS
    cP
    cR
    c.1
    @56
    chp0mat.p
    chpidmat.s
    chpidmat.1
    @56
    eqid
    #
    ply1scl1
    @26
    @53
    @56
    @48
    wcel
    @54
    @48
    cP
    @56
    @55
    @57
    ringidcl
    syl
    eqeltrd
    3jca
    syl
    adantl
    @48
    cP
    @7
    cX
    @12
    @55
    @37
    grpsubcl
    syl
    @48
    cP
    cG
    chp0mat.g
    @55
    mgpbas
    syl6eleq
    @45
    @0
    @47
    w3a
    @40
    @11
    @38
    c.ex
    co
    @14
    cN
    @46
    c.ex
    vk
    cG
    @38
    @46
    eqid
    chp0mat.m
    gsumconst
    @38
    @13
    @11
    c.ex
    @7
    c.mi
    cX
    @12
    c.mi
    @7
    chpidmat.m
    eqcomi
    oveqi
    oveq2i
    syl6eq
    syl3anc
    eqtrd
    eqtrd
end
