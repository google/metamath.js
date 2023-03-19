include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "c0g.mm"
include "cfsupp.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "ovexd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "clt.mm"
include "wbr.mm"
include "csb.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cbs.mm"
include "eqid.mm"
include "chpmatply1.mm"
include "syl5eqel.mm"
include "coe1fvalcl.mm"
include "sylan.mm"
include "crg.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "mptcoe1fsupp.mm"
include "syl2anc.mm"
include "mptnn0fsuppr.mm"
include "csca.mm"
include "csbfv.mm"
include "a1i.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "matsca2.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "clmod.mm"
include "matlmod.mm"
include "sylan2.mm"
include "matring.mm"
include "ringidcl.mm"
include "syl.mm"
include "lmod0vs.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "mptnn0fsuppd.mm"
include "syl5eqbr.mm"

theorem cpmidpmatlem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cL: class L
  let vl: setvar l
  let vs: setvar s
  let vn: setvar n
  let vx: setvar x
  assume cpmidgsum.a: |- A = ( N Mat R )
  assume cpmidgsum.b: |- B = ( Base ` A )
  assume cpmidgsum.p: |- P = ( Poly1 ` R )
  assume cpmidgsum.y: |- Y = ( N Mat P )
  assume cpmidgsum.x: |- X = ( var1 ` R )
  assume cpmidgsum.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume cpmidgsum.m: |- .x. = ( .s ` Y )
  assume cpmidgsum.1: |- .1. = ( 1r ` Y )
  assume cpmidgsum.u: |- U = ( algSc ` P )
  assume cpmidgsum.c: |- C = ( N CharPlyMat R )
  assume cpmidgsum.k: |- K = ( C ` M )
  assume cpmidgsum.h: |- H = ( K .x. .1. )
  assume cpmidgsumm2pm.o: |- O = ( 1r ` A )
  assume cpmidgsumm2pm.m: |- .* = ( .s ` A )
  assume cpmidgsumm2pm.t: |- T = ( N matToPolyMat R )
  assume cpmidpmat.g: |- G = ( k e. NN0 |-> ( ( ( coe1 ` K ) ` k ) .* O ) )

  disjoint K k
  disjoint O k
  disjoint .* k
  disjoint M k
  disjoint N k
  disjoint B k
  disjoint H k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint Y k
  disjoint L k
  disjoint A l
  disjoint A s
  disjoint l s
  disjoint B l
  disjoint B s
  disjoint K l
  disjoint K s
  disjoint M l
  disjoint M s
  disjoint N n
  disjoint N s
  disjoint k n
  disjoint k s
  disjoint n s
  disjoint O l
  disjoint O s
  disjoint R l
  disjoint R s
  disjoint .* l
  disjoint .* s
  disjoint A n
  disjoint B n
  disjoint k n
  disjoint H n
  disjoint K n
  disjoint X n
  disjoint N l
  disjoint N n
  disjoint N x
  disjoint k l
  disjoint k x
  disjoint l n
  disjoint l x
  disjoint n x
  disjoint P n
  disjoint R n
  disjoint Y l
  disjoint Y n
  disjoint .^ n
  disjoint M n
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> G finSupp ( 0g ` A ) )

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
    cG
    vk
    cn0
    vk
    cv
    #
    cK
    cco1
    cfv
    #
    cfv
    #
    cO
    c.as
    co
    #
    cmpt
    cA
    c0g
    cfv
    #
    cfsupp
    cpmidpmat.g
    @3
    vl
    cvv
    @7
    vl
    cv
    #
    @5
    cfv
    #
    cO
    c.as
    co
    #
    vk
    cvv
    @8
    vs
    @3
    cA
    c0g
    fvexd
    @3
    @4
    cn0
    wcel
    wa
    @6
    cO
    c.as
    ovexd
    @4
    @9
    wceq
    @6
    @10
    cO
    c.as
    @4
    @9
    @5
    fveq2
    oveq1d
    @3
    vs
    cv
    @9
    clt
    wbr
    #
    vn
    @9
    vn
    cv
    #
    @5
    cfv
    #
    csb
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vl
    cn0
    wral
    #
    vs
    cn0
    wrex
    @12
    @11
    @8
    wceq
    #
    wi
    #
    vl
    cn0
    wral
    #
    vs
    cn0
    wrex
    @3
    vl
    cR
    cbs
    cfv
    #
    @14
    vn
    cvv
    @16
    vs
    @3
    cR
    c0g
    fvexd
    @3
    cK
    cP
    cbs
    cfv
    #
    wcel
    #
    @13
    cn0
    wcel
    @14
    @23
    wcel
    @3
    cK
    cM
    cC
    cfv
    @24
    cpmidgsum.k
    cA
    cB
    cC
    cP
    cR
    @24
    cM
    cN
    cpmidgsum.c
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    @24
    eqid
    #
    chpmatply1
    syl5eqel
    #
    @5
    @24
    cP
    cR
    cK
    @23
    @13
    @5
    eqid
    @26
    cpmidgsum.p
    @23
    eqid
    coe1fvalcl
    sylan
    @3
    cR
    crg
    wcel
    #
    @25
    vn
    cn0
    @14
    cmpt
    @16
    cfsupp
    wbr
    @1
    @0
    @28
    @2
    cR
    crngring
    #
    3ad2ant2
    @27
    @24
    cP
    cR
    vn
    cK
    @16
    cpmidgsum.p
    @26
    @16
    eqid
    mptcoe1fsupp
    syl2anc
    mptnn0fsuppr
    @3
    @19
    @22
    vs
    cn0
    @3
    @18
    @21
    vl
    cn0
    @3
    @9
    cn0
    wcel
    #
    wa
    #
    @17
    @20
    @12
    @31
    @17
    @20
    @31
    @17
    wa
    #
    @11
    cA
    csca
    cfv
    #
    c0g
    cfv
    #
    cO
    c.as
    co
    #
    @8
    @32
    @10
    @34
    cO
    c.as
    @32
    @10
    @16
    @34
    @31
    @17
    @10
    @16
    wceq
    @31
    @15
    @10
    @16
    @15
    @10
    wceq
    @31
    vn
    @9
    @5
    csbfv
    a1i
    eqeq1d
    biimpa
    @32
    cR
    @33
    c0g
    @3
    cR
    @33
    wceq
    #
    @30
    @17
    @0
    @1
    @36
    @2
    cA
    cR
    cN
    ccrg
    cpmidgsum.a
    matsca2
    3adant3
    ad2antrr
    fveq2d
    eqtrd
    oveq1d
    @3
    @35
    @8
    wceq
    #
    @30
    @17
    @3
    cA
    clmod
    wcel
    #
    cO
    cB
    wcel
    #
    @37
    @0
    @1
    @38
    @2
    @1
    @0
    @28
    @38
    @29
    cA
    cR
    cN
    cpmidgsum.a
    matlmod
    sylan2
    3adant3
    @0
    @1
    @39
    @2
    @0
    @1
    wa
    cA
    crg
    wcel
    #
    @39
    @1
    @0
    @28
    @40
    @29
    cA
    cR
    cN
    cpmidgsum.a
    matring
    sylan2
    cB
    cA
    cO
    cpmidgsum.b
    cpmidgsumm2pm.o
    ringidcl
    syl
    3adant3
    c.as
    @33
    @34
    cB
    cA
    cO
    @8
    cpmidgsum.b
    @33
    eqid
    cpmidgsumm2pm.m
    @34
    eqid
    @8
    eqid
    lmod0vs
    syl2anc
    ad2antrr
    eqtrd
    ex
    imim2d
    ralimdva
    reximdv
    mpd
    mptnn0fsuppd
    syl5eqbr
end
