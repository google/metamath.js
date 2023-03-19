include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "cmulr.mm"
include "crh.mm"
include "cbs.mm"
include "csca.mm"
include "casa.mm"
include "simpr.mm"
include "ply1assa.mm"
include "eqid.mm"
include "asclrhm.mm"
include "3syl.mm"
include "ply1sca.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "adantr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simplrr.mm"
include "matecld.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "crg.mm"
include "crngring.mm"
include "matvscacell.mm"
include "fveq2d.mm"
include "w3a.mm"
include "anim2i.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "mat2pmatvalel.mm"
include "sylan.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "simpll.mm"
include "matvscl.mm"
include "syl31anc.mm"
include "ply1ring.mm"
include "syl.mm"
include "simpl.mm"
include "ply1sclcl.mm"
include "syl2an.mm"
include "mat2pmatbas0.mm"
include "jca.mm"
include "ralrimivva.mm"
include "wb.mm"
include "syl21anc.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem mat2pmatlin
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cH: class H
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )
  assume mat2pmatlin.k: |- K = ( Base ` R )
  assume mat2pmatlin.s: |- S = ( algSc ` P )
  assume mat2pmatlin.m: |- .x. = ( .s ` A )
  assume mat2pmatlin.n: |- .X. = ( .s ` C )


  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( X e. K /\ Y e. B ) ) -> ( T ` ( X .x. Y ) ) = ( ( S ` X ) .X. ( T ` Y ) ) )

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
    cX
    cK
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.x
    co
    #
    cT
    cfv
    #
    cX
    cS
    cfv
    #
    cY
    cT
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    @8
    co
    #
    @13
    @14
    @11
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @6
    @17
    vi
    vj
    cN
    cN
    @6
    @13
    cN
    wcel
    #
    @14
    cN
    wcel
    #
    wa
    #
    wa
    #
    @13
    @14
    @7
    co
    #
    cS
    cfv
    #
    @9
    @13
    @14
    @10
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    @15
    @16
    @22
    cX
    @13
    @14
    cY
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cS
    cfv
    #
    @9
    @28
    cS
    cfv
    #
    @26
    co
    #
    @24
    @27
    @22
    cS
    cR
    cP
    crh
    co
    #
    wcel
    #
    cX
    cR
    cbs
    cfv
    #
    wcel
    #
    @28
    @36
    wcel
    @31
    @33
    wceq
    @6
    @35
    @21
    @2
    @35
    @5
    @2
    cS
    cP
    csca
    cfv
    #
    cP
    crh
    co
    #
    @34
    @2
    @1
    cP
    casa
    wcel
    cS
    @39
    wcel
    @0
    @1
    simpr
    cP
    cR
    mat2pmatbas.p
    ply1assa
    cS
    @38
    cP
    mat2pmatlin.s
    @38
    eqid
    asclrhm
    3syl
    @2
    cR
    @38
    cP
    crh
    @1
    cR
    @38
    wceq
    @0
    cP
    cR
    ccrg
    mat2pmatbas.p
    ply1sca
    adantl
    oveq1d
    eleqtrrd
    adantr
    adantr
    @5
    @37
    @2
    @21
    @3
    @37
    @4
    @3
    @37
    cK
    @36
    cX
    mat2pmatlin.k
    eleq2i
    biimpi
    adantr
    ad2antlr
    @22
    cA
    cB
    cR
    @13
    @14
    @36
    cY
    cN
    mat2pmatbas.a
    @36
    eqid
    #
    mat2pmatbas.b
    @6
    @19
    @20
    simprl
    @21
    @20
    @6
    @19
    @20
    simpr
    adantl
    @2
    @3
    @4
    @21
    simplrr
    matecld
    cX
    @28
    cR
    cP
    @29
    @26
    cS
    @36
    @40
    @29
    eqid
    #
    @26
    eqid
    #
    rhmmul
    syl3anc
    @22
    @23
    @30
    cS
    @22
    cR
    crg
    wcel
    #
    @5
    @21
    @23
    @30
    wceq
    @6
    @43
    @21
    @1
    @43
    @0
    @5
    cR
    crngring
    #
    ad2antlr
    #
    adantr
    #
    @6
    @5
    @21
    @2
    @5
    simpr
    adantr
    @6
    @21
    simpr
    #
    cA
    cB
    cR
    c.x
    @29
    @13
    @14
    cK
    cN
    cX
    cY
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatlin.k
    mat2pmatlin.m
    @41
    matvscacell
    syl3anc
    fveq2d
    @22
    @25
    @32
    @9
    @26
    @6
    @0
    @43
    @4
    w3a
    #
    @21
    @25
    @32
    wceq
    @6
    @0
    @43
    wa
    #
    @4
    wa
    @48
    @2
    @49
    @5
    @4
    @1
    @43
    @0
    @44
    anim2i
    #
    @3
    @4
    simpr
    anim12i
    @0
    @43
    @4
    df-3an
    sylibr
    #
    cA
    cB
    cP
    cR
    cS
    cT
    cY
    cN
    crg
    @13
    @14
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatlin.s
    mat2pmatvalel
    sylan
    oveq2d
    3eqtr4d
    @22
    @0
    @43
    @7
    cB
    wcel
    #
    @21
    @15
    @24
    wceq
    @6
    @0
    @21
    @0
    @1
    @5
    simpll
    #
    adantr
    @46
    @6
    @52
    @21
    @2
    @49
    @5
    @52
    @50
    cA
    cB
    cX
    cR
    c.x
    cK
    cN
    cY
    mat2pmatlin.k
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatlin.m
    matvscl
    sylan
    #
    adantr
    @47
    cA
    cB
    cP
    cR
    cS
    cT
    @7
    cN
    crg
    @13
    @14
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatlin.s
    mat2pmatvalel
    syl31anc
    @22
    cP
    crg
    wcel
    #
    @9
    cP
    cbs
    cfv
    #
    wcel
    #
    @10
    cH
    wcel
    #
    wa
    #
    @21
    @16
    @27
    wceq
    @6
    @55
    @21
    @1
    @55
    @0
    @5
    @1
    @43
    @55
    @44
    cP
    cR
    mat2pmatbas.p
    ply1ring
    syl
    ad2antlr
    #
    adantr
    @6
    @59
    @21
    @6
    @57
    @58
    @2
    @43
    @3
    @57
    @5
    @1
    @43
    @0
    @44
    adantl
    @3
    @4
    simpl
    cS
    @56
    cP
    cR
    cX
    cK
    mat2pmatbas.p
    mat2pmatlin.s
    mat2pmatlin.k
    @56
    eqid
    #
    ply1sclcl
    syl2an
    @6
    @48
    @58
    @51
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    cY
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatbas0
    syl
    jca
    #
    adantr
    @47
    cC
    cH
    cP
    c.xp
    @26
    @13
    @14
    @56
    cN
    @9
    @10
    mat2pmatbas.c
    mat2pmatbas0.h
    @61
    mat2pmatlin.n
    @42
    matvscacell
    syl3anc
    3eqtr4d
    ralrimivva
    @6
    @8
    cH
    wcel
    #
    @11
    cH
    wcel
    #
    @12
    @18
    wb
    @6
    @0
    @43
    @52
    @63
    @53
    @45
    @54
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    @7
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatbas0
    syl3anc
    @6
    @0
    @55
    @59
    @64
    @53
    @60
    @62
    cC
    cH
    @9
    cP
    c.xp
    @56
    cN
    @10
    @61
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatlin.n
    matvscl
    syl21anc
    cC
    cH
    cP
    vi
    vj
    cN
    @8
    @11
    mat2pmatbas.c
    mat2pmatbas0.h
    eqmat
    syl2anc
    mpbird
end
