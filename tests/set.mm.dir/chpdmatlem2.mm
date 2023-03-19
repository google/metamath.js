include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cmulr.mm"
include "c0g.mm"
include "cbs.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "ad4antr.mm"
include "chpdmatlem0.mm"
include "3adant3.mm"
include "mat2pmatbas.mm"
include "simpr.mm"
include "anim1i.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "matsubgcell.mm"
include "syl121anc.mm"
include "vr1cl.mm"
include "pmatring.mm"
include "ringidcl.mm"
include "syl.mm"
include "jca.mm"
include "3jca.mm"
include "matvscacell.mm"
include "oveq1d.mm"
include "weq.mm"
include "cur.mm"
include "cif.mm"
include "simpll1.mm"
include "adantr.mm"
include "mat1ov.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "eqtrd.mm"
include "simpll.mm"
include "mat2pmatvalel.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "adantl.mm"
include "ply1scl0.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "jccir.mm"
include "grpsubid.mm"
include "3eqtrd.mm"

theorem chpdmatlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume chpdmat.c: |- C = ( N CharPlyMat R )
  assume chpdmat.p: |- P = ( Poly1 ` R )
  assume chpdmat.a: |- A = ( N Mat R )
  assume chpdmat.s: |- S = ( algSc ` P )
  assume chpdmat.b: |- B = ( Base ` A )
  assume chpdmat.x: |- X = ( var1 ` R )
  assume chpdmat.0: |- .0. = ( 0g ` R )
  assume chpdmat.g: |- G = ( mulGrp ` P )
  assume chpdmat.m: |- .- = ( -g ` P )
  assume chpdmatlem.q: |- Q = ( N Mat P )
  assume chpdmatlem.1: |- .1. = ( 1r ` Q )
  assume chpdmatlem.m: |- .x. = ( .s ` Q )
  assume chpdmatlem.z: |- Z = ( -g ` Q )
  assume chpdmatlem.t: |- T = ( N matToPolyMat R )


  assert |- ( ( ( ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ i e. N ) /\ j e. N ) /\ i =/= j ) /\ ( i M j ) = .0. ) -> ( i ( ( X .x. .1. ) Z ( T ` M ) ) j ) = ( 0g ` P ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vi
    cv
    #
    cN
    wcel
    #
    wa
    #
    vj
    cv
    #
    cN
    wcel
    #
    wa
    #
    @4
    @7
    wne
    #
    wa
    #
    @4
    @7
    cM
    co
    #
    c.0
    wceq
    #
    wa
    #
    @4
    @7
    cX
    c.1
    c.x
    co
    #
    cM
    cT
    cfv
    #
    cZ
    co
    co
    #
    @4
    @7
    @15
    co
    #
    @4
    @7
    @16
    co
    #
    c.mi
    co
    #
    cX
    @4
    @7
    c.1
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    @19
    c.mi
    co
    #
    cP
    c0g
    cfv
    #
    @14
    cP
    crg
    wcel
    #
    @15
    cQ
    cbs
    cfv
    #
    wcel
    #
    @16
    @27
    wcel
    #
    @5
    @8
    wa
    #
    @17
    @20
    wceq
    @3
    @26
    @5
    @8
    @10
    @13
    @1
    @0
    @26
    @2
    cP
    cR
    chpdmat.p
    ply1ring
    #
    3ad2ant2
    #
    ad4antr
    @3
    @28
    @5
    @8
    @10
    @13
    @0
    @1
    @28
    @2
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    c.x
    c.1
    cG
    c.mi
    cN
    cX
    c.0
    chpdmat.c
    chpdmat.p
    chpdmat.a
    chpdmat.s
    chpdmat.b
    chpdmat.x
    chpdmat.0
    chpdmat.g
    chpdmat.m
    chpdmatlem.q
    chpdmatlem.1
    chpdmatlem.m
    chpdmatlem0
    3adant3
    ad4antr
    @3
    @29
    @5
    @8
    @10
    @13
    cA
    cB
    cQ
    cP
    cR
    cT
    cM
    cN
    chpdmatlem.t
    chpdmat.a
    chpdmat.b
    chpdmat.p
    chpdmatlem.q
    mat2pmatbas
    ad4antr
    @9
    @30
    @10
    @13
    @6
    @5
    @8
    @3
    @5
    simpr
    #
    anim1i
    #
    ad2antrr
    cQ
    @27
    cP
    cZ
    @4
    @7
    c.mi
    cN
    @15
    @16
    chpdmatlem.q
    @27
    eqid
    #
    chpdmatlem.z
    chpdmat.m
    matsubgcell
    syl121anc
    @14
    @18
    @23
    @19
    c.mi
    @14
    @26
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    c.1
    @27
    wcel
    #
    wa
    #
    @30
    w3a
    #
    @18
    @23
    wceq
    @9
    @40
    @10
    @13
    @9
    @26
    @39
    @30
    @3
    @26
    @5
    @8
    @32
    ad2antrr
    #
    @3
    @39
    @5
    @8
    @3
    @37
    @38
    @1
    @0
    @37
    @2
    @36
    cP
    cR
    cX
    chpdmat.x
    chpdmat.p
    @36
    eqid
    #
    vr1cl
    #
    3ad2ant2
    @3
    cQ
    crg
    wcel
    #
    @38
    @0
    @1
    @44
    @2
    cQ
    cP
    cR
    cN
    chpdmat.p
    chpdmatlem.q
    pmatring
    3adant3
    @27
    cQ
    c.1
    @35
    chpdmatlem.1
    ringidcl
    syl
    jca
    ad2antrr
    @34
    3jca
    ad2antrr
    cQ
    @27
    cP
    c.x
    @22
    @4
    @7
    @36
    cN
    cX
    c.1
    chpdmatlem.q
    @35
    @42
    chpdmatlem.m
    @22
    eqid
    #
    matvscacell
    syl
    oveq1d
    @14
    @24
    @25
    @12
    cS
    cfv
    #
    c.mi
    co
    @25
    @25
    c.mi
    co
    #
    @25
    @14
    @23
    @25
    @19
    @46
    c.mi
    @11
    @23
    @25
    wceq
    @13
    @11
    @23
    cX
    @25
    @22
    co
    #
    @25
    @11
    @21
    @25
    cX
    @22
    @9
    @10
    @21
    vi
    vj
    weq
    cP
    cur
    cfv
    #
    @25
    cif
    @25
    @9
    cQ
    cP
    c.1
    @49
    @4
    @7
    cN
    @25
    chpdmatlem.q
    @49
    eqid
    @25
    eqid
    #
    @0
    @1
    @2
    @5
    @8
    simpll1
    @41
    @6
    @5
    @8
    @33
    adantr
    @6
    @8
    simpr
    chpdmatlem.1
    mat1ov
    @4
    @7
    @49
    @25
    ifnefalse
    sylan9eq
    oveq2d
    @6
    @48
    @25
    wceq
    #
    @8
    @10
    @3
    @51
    @5
    @3
    @26
    @37
    wa
    #
    @51
    @1
    @0
    @52
    @2
    @1
    @26
    @37
    @31
    @43
    jca
    3ad2ant2
    @36
    cP
    @22
    cX
    @25
    @42
    @45
    @50
    ringrz
    syl
    adantr
    ad2antrr
    eqtrd
    adantr
    @14
    @3
    @30
    wa
    #
    @19
    @46
    wceq
    @9
    @53
    @10
    @13
    @9
    @3
    @30
    @3
    @5
    @8
    simpll
    @34
    jca
    ad2antrr
    cA
    cB
    cP
    cR
    cS
    cT
    cM
    cN
    crg
    @4
    @7
    chpdmatlem.t
    chpdmat.a
    chpdmat.b
    chpdmat.p
    chpdmat.s
    mat2pmatvalel
    syl
    oveq12d
    @14
    @46
    @25
    @25
    c.mi
    @14
    @46
    c.0
    cS
    cfv
    #
    @25
    @13
    @46
    @54
    wceq
    @11
    @12
    c.0
    cS
    fveq2
    adantl
    @3
    @54
    @25
    wceq
    #
    @5
    @8
    @10
    @13
    @1
    @0
    @55
    @2
    cS
    cP
    cR
    @25
    c.0
    chpdmat.p
    chpdmat.s
    chpdmat.0
    @50
    ply1scl0
    3ad2ant2
    ad4antr
    eqtrd
    oveq2d
    @3
    @47
    @25
    wceq
    #
    @5
    @8
    @10
    @13
    @3
    cP
    cgrp
    wcel
    #
    @25
    @36
    wcel
    #
    wa
    #
    @56
    @1
    @0
    @59
    @2
    @1
    @57
    @58
    @1
    @26
    @57
    @31
    cP
    ringgrp
    syl
    @36
    cP
    @25
    @42
    @50
    grpidcl
    jccir
    3ad2ant2
    @36
    cP
    c.mi
    @25
    @25
    @42
    @50
    chpdmat.m
    grpsubid
    syl
    ad4antr
    3eqtrd
    3eqtrd
end
