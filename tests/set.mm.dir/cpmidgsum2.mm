include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cn0.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "cpmadugsum.mm"
include "wa.mm"
include "cmdat.mm"
include "cbs.mm"
include "cgrp.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pmatring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "clmod.mm"
include "csca.mm"
include "pmatlmod.mm"
include "sylan2.mm"
include "adantl.mm"
include "eqid.mm"
include "vr1cl.mm"
include "syl.mm"
include "ply1crng.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "ringidcl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "grpsubcl.mm"
include "3ad2ant2.mm"
include "madurid.mm"
include "syl2anc.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "mp1i.mm"
include "chpmatval.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "3eqtr4rd.mm"
include "adantr.mm"
include "simpr.mm"
include "eqtrd.mm"
include "ex.mm"
include "reximdv.mm"
include "mpd.mm"

theorem cpmidgsum2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let vi: setvar i
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vx: setvar x
  assume cpmadugsum.a: |- A = ( N Mat R )
  assume cpmadugsum.b: |- B = ( Base ` A )
  assume cpmadugsum.p: |- P = ( Poly1 ` R )
  assume cpmadugsum.y: |- Y = ( N Mat P )
  assume cpmadugsum.t: |- T = ( N matToPolyMat R )
  assume cpmadugsum.x: |- X = ( var1 ` R )
  assume cpmadugsum.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume cpmadugsum.m: |- .x. = ( .s ` Y )
  assume cpmadugsum.r: |- .X. = ( .r ` Y )
  assume cpmadugsum.1: |- .1. = ( 1r ` Y )
  assume cpmadugsum.g: |- .+ = ( +g ` Y )
  assume cpmadugsum.s: |- .- = ( -g ` Y )
  assume cpmadugsum.i: |- I = ( ( X .x. .1. ) .- ( T ` M ) )
  assume cpmadugsum.j: |- J = ( N maAdju P )
  assume cpmadugsum.0: |- .0. = ( 0g ` Y )
  assume cpmadugsum.g2: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cpmidgsum2.c: |- C = ( N CharPlyMat R )
  assume cpmidgsum2.k: |- K = ( C ` M )
  assume cpmidgsum2.h: |- H = ( K .x. .1. )

  disjoint B i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint X i
  disjoint Y i
  disjoint .X. i
  disjoint .x. i
  disjoint .1. i
  disjoint b i
  disjoint i s
  disjoint T i
  disjoint .^ i
  disjoint .- i
  disjoint A b
  disjoint A n
  disjoint A s
  disjoint b n
  disjoint b s
  disjoint n s
  disjoint B b
  disjoint B n
  disjoint B s
  disjoint I b
  disjoint I i
  disjoint I n
  disjoint I s
  disjoint i n
  disjoint J b
  disjoint J i
  disjoint J n
  disjoint J s
  disjoint M b
  disjoint M n
  disjoint M s
  disjoint N b
  disjoint N n
  disjoint N s
  disjoint P i
  disjoint P n
  disjoint R b
  disjoint R n
  disjoint R s
  disjoint T b
  disjoint T n
  disjoint T s
  disjoint X b
  disjoint X n
  disjoint X s
  disjoint Y b
  disjoint Y n
  disjoint Y s
  disjoint .^ n
  disjoint .^ s
  disjoint .^ b
  disjoint .x. b
  disjoint .x. n
  disjoint .x. s
  disjoint G i
  disjoint .X. n
  disjoint .0. n
  disjoint .- n
  disjoint B x
  disjoint M x
  disjoint N x
  disjoint R x
  disjoint T x
  disjoint X x
  disjoint .x. x
  disjoint .^ x
  disjoint i x
  disjoint b x
  disjoint s x
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) H = ( Y gsum ( i e. NN0 |-> ( ( i .^ X ) .x. ( G ` i ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cI
    cI
    cJ
    cfv
    #
    c.xp
    co
    #
    cY
    vi
    cn0
    vi
    cv
    #
    cX
    c.ex
    co
    @6
    cG
    cfv
    c.x
    co
    cmpt
    cgsu
    co
    #
    wceq
    #
    vb
    cB
    cc0
    vs
    cv
    cfz
    co
    cmap
    co
    #
    wrex
    #
    vs
    cn
    wrex
    cH
    @7
    wceq
    #
    vb
    @9
    wrex
    #
    vs
    cn
    wrex
    cA
    cB
    cP
    c.pl
    cR
    cT
    c.x
    c.xp
    c.1
    vi
    vn
    c.ex
    cG
    cI
    cJ
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    cpmadugsum.t
    cpmadugsum.x
    cpmadugsum.e
    cpmadugsum.m
    cpmadugsum.r
    cpmadugsum.1
    cpmadugsum.g
    cpmadugsum.s
    cpmadugsum.i
    cpmadugsum.j
    cpmadugsum.0
    cpmadugsum.g2
    cpmadugsum
    @3
    @10
    @12
    vs
    cn
    @3
    @8
    @11
    vb
    @9
    @3
    @8
    @11
    @3
    @8
    wa
    cH
    @5
    @7
    @3
    cH
    @5
    wceq
    @8
    @3
    cX
    c.1
    c.x
    co
    #
    cM
    cT
    cfv
    #
    c.mi
    co
    #
    @15
    cJ
    cfv
    #
    c.xp
    co
    #
    @15
    cN
    cP
    cmdat
    co
    #
    cfv
    #
    c.1
    c.x
    co
    #
    @5
    cH
    @3
    @15
    cY
    cbs
    cfv
    #
    wcel
    #
    cP
    ccrg
    wcel
    #
    @17
    @20
    wceq
    @3
    cY
    cgrp
    wcel
    #
    @13
    @21
    wcel
    #
    @14
    @21
    wcel
    #
    @22
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    cY
    crg
    wcel
    #
    @24
    @0
    @1
    @28
    @2
    @1
    @27
    @0
    cR
    crngring
    #
    anim2i
    #
    3adant3
    cY
    cP
    cR
    cN
    cpmadugsum.p
    cpmadugsum.y
    pmatring
    #
    cY
    ringgrp
    3syl
    @0
    @1
    @25
    @2
    @0
    @1
    wa
    #
    cY
    clmod
    wcel
    #
    cX
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    c.1
    @21
    wcel
    #
    @25
    @1
    @0
    @27
    @34
    @30
    cY
    cP
    cR
    cN
    cpmadugsum.p
    cpmadugsum.y
    pmatlmod
    sylan2
    @33
    cX
    cP
    cbs
    cfv
    #
    @36
    @33
    @27
    cX
    @38
    wcel
    @1
    @27
    @0
    @30
    adantl
    @38
    cP
    cR
    cX
    cpmadugsum.x
    cpmadugsum.p
    @38
    eqid
    vr1cl
    syl
    @33
    cP
    @35
    cbs
    @1
    @0
    @23
    cP
    @35
    wceq
    cP
    cR
    cpmadugsum.p
    ply1crng
    #
    cY
    cP
    cN
    ccrg
    cpmadugsum.y
    matsca2
    sylan2
    fveq2d
    eleqtrd
    @33
    @28
    @29
    @37
    @31
    @32
    @21
    cY
    c.1
    @21
    eqid
    #
    cpmadugsum.1
    ringidcl
    3syl
    cX
    c.x
    @35
    @36
    @21
    cY
    c.1
    @40
    @35
    eqid
    cpmadugsum.m
    @36
    eqid
    lmodvscl
    syl3anc
    3adant3
    @1
    @0
    @27
    @2
    @26
    @30
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    cpmadugsum.t
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    mat2pmatbas
    syl3an2
    @21
    cY
    c.mi
    @13
    @14
    @40
    cpmadugsum.s
    grpsubcl
    syl3anc
    @1
    @0
    @23
    @2
    @39
    3ad2ant2
    cY
    @21
    @18
    cP
    c.x
    c.xp
    c.1
    cJ
    @15
    cN
    cpmadugsum.y
    @40
    cpmadugsum.j
    @18
    eqid
    #
    cpmadugsum.1
    cpmadugsum.r
    cpmadugsum.m
    madurid
    syl2anc
    cI
    @15
    wceq
    #
    @5
    @17
    wceq
    @3
    cpmadugsum.i
    @42
    cI
    @15
    @4
    @16
    c.xp
    @42
    id
    cI
    @15
    cJ
    fveq2
    oveq12d
    mp1i
    @3
    cH
    cK
    c.1
    c.x
    co
    @20
    cpmidgsum2.h
    @3
    cK
    @19
    c.1
    c.x
    @3
    cK
    cM
    cC
    cfv
    @19
    cpmidgsum2.k
    cA
    cB
    cC
    @18
    cP
    cR
    cT
    c.x
    c.1
    cM
    c.mi
    cN
    ccrg
    cX
    cY
    cpmidgsum2.c
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    @41
    cpmadugsum.s
    cpmadugsum.x
    cpmadugsum.m
    cpmadugsum.t
    cpmadugsum.1
    chpmatval
    syl5eq
    oveq1d
    syl5eq
    3eqtr4rd
    adantr
    @3
    @8
    simpr
    eqtrd
    ex
    reximdv
    reximdv
    mpd
end
