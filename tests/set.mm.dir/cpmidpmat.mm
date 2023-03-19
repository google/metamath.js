include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cpmidgsumm2pm.mm"
include "fveq2d.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "cpmidpmatlem1.mm"
include "eqcomd.mm"
include "adantl.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "cmap.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "3simpa.mm"
include "cpmidpmatlem2.mm"
include "cpmidpmatlem3.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "eleq1i.mm"
include "breq1i.mm"
include "anbi12i.mm"
include "pm2mp.mm"
include "sylan2b.mm"
include "syl12anc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "mpteq2i.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem cpmidpmat
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cH: class H
  let cI: class I
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vl: setvar l
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
  assume cpmidgsum.w: |- W = ( Base ` Y )
  assume cpmidpmat.p: |- Q = ( Poly1 ` A )
  assume cpmidpmat.z: |- Z = ( var1 ` A )
  assume cpmidpmat.m: |- .xb = ( .s ` Q )
  assume cpmidpmat.e: |- E = ( .g ` ( mulGrp ` Q ) )
  assume cpmidpmat.i: |- I = ( N pMatToMatPoly R )

  disjoint A n
  disjoint B n
  disjoint H n
  disjoint K n
  disjoint X n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint Y n
  disjoint .^ n
  disjoint M n
  disjoint I n
  disjoint O n
  disjoint T n
  disjoint W n
  disjoint .* n
  disjoint .x. n
  disjoint B k
  disjoint k n
  disjoint H k
  disjoint N k
  disjoint N l
  disjoint N x
  disjoint k l
  disjoint k x
  disjoint l n
  disjoint l x
  disjoint n x
  disjoint P k
  disjoint R k
  disjoint Y k
  disjoint Y l
  disjoint K k
  disjoint K x
  disjoint M k
  disjoint O k
  disjoint O x
  disjoint .* k
  disjoint .* x
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( I ` H ) = ( Q gsum ( n e. NN0 |-> ( ( ( ( coe1 ` K ) ` n ) .* O ) .xb ( n E Z ) ) ) ) )

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
    cH
    cI
    cfv
    cY
    vn
    cn0
    vn
    cv
    #
    cX
    c.ex
    co
    #
    @4
    cK
    cco1
    cfv
    #
    cfv
    cO
    c.as
    co
    #
    cT
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cI
    cfv
    #
    cQ
    vn
    cn0
    @4
    vk
    cn0
    vk
    cv
    #
    @6
    cfv
    #
    cO
    c.as
    co
    #
    cmpt
    #
    cfv
    #
    @4
    cZ
    cE
    co
    #
    c.xb
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cQ
    vn
    cn0
    @7
    @18
    c.xb
    co
    #
    cmpt
    #
    cgsu
    co
    @3
    cH
    @11
    cI
    cA
    cB
    cC
    cP
    cR
    cT
    c.x
    cU
    c.1
    vn
    c.ex
    cH
    c.as
    cK
    cM
    cN
    cO
    cX
    cY
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    cpmidgsum.x
    cpmidgsum.e
    cpmidgsum.m
    cpmidgsum.1
    cpmidgsum.u
    cpmidgsum.c
    cpmidgsum.k
    cpmidgsum.h
    cpmidgsumm2pm.o
    cpmidgsumm2pm.m
    cpmidgsumm2pm.t
    cpmidgsumm2pm
    fveq2d
    @3
    @12
    cY
    vn
    cn0
    @5
    @17
    cT
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cI
    cfv
    #
    @21
    @3
    @11
    @27
    cI
    @3
    @10
    @26
    cY
    cgsu
    @3
    vn
    cn0
    @9
    @25
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @8
    @24
    @5
    c.x
    @30
    @7
    @17
    cT
    @29
    @7
    @17
    wceq
    @3
    @29
    @17
    @7
    cA
    cB
    cC
    cP
    cR
    cT
    c.x
    cU
    c.1
    vk
    c.ex
    @16
    cH
    c.as
    cK
    @4
    cM
    cN
    cO
    cX
    cY
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    cpmidgsum.x
    cpmidgsum.e
    cpmidgsum.m
    cpmidgsum.1
    cpmidgsum.u
    cpmidgsum.c
    cpmidgsum.k
    cpmidgsum.h
    cpmidgsumm2pm.o
    cpmidgsumm2pm.m
    cpmidgsumm2pm.t
    @16
    eqid
    #
    cpmidpmatlem1
    #
    eqcomd
    adantl
    fveq2d
    oveq2d
    mpteq2dva
    oveq2d
    fveq2d
    @3
    cY
    vn
    cn0
    @5
    @4
    vx
    cn0
    vx
    cv
    #
    @6
    cfv
    #
    cO
    c.as
    co
    #
    cmpt
    #
    cfv
    #
    cT
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cI
    cfv
    #
    cQ
    vn
    cn0
    @37
    @18
    c.xb
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @28
    @21
    @3
    @0
    @1
    wa
    #
    @16
    cB
    cn0
    cmap
    co
    #
    wcel
    #
    @16
    cA
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @42
    @45
    wceq
    #
    @0
    @1
    @2
    3simpa
    cA
    cB
    cC
    cP
    cR
    cT
    c.x
    cU
    c.1
    vk
    c.ex
    @16
    cH
    c.as
    cK
    cM
    cN
    cO
    cX
    cY
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    cpmidgsum.x
    cpmidgsum.e
    cpmidgsum.m
    cpmidgsum.1
    cpmidgsum.u
    cpmidgsum.c
    cpmidgsum.k
    cpmidgsum.h
    cpmidgsumm2pm.o
    cpmidgsumm2pm.m
    cpmidgsumm2pm.t
    @31
    cpmidpmatlem2
    cA
    cB
    cC
    cP
    cR
    cT
    c.x
    cU
    c.1
    vk
    c.ex
    @16
    cH
    c.as
    cK
    cM
    cN
    cO
    cX
    cY
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    cpmidgsum.x
    cpmidgsum.e
    cpmidgsum.m
    cpmidgsum.1
    cpmidgsum.u
    cpmidgsum.c
    cpmidgsum.k
    cpmidgsum.h
    cpmidgsumm2pm.o
    cpmidgsumm2pm.m
    cpmidgsumm2pm.t
    @31
    cpmidpmatlem3
    @48
    @50
    wa
    @46
    @36
    @47
    wcel
    #
    @36
    @49
    cfsupp
    wbr
    #
    wa
    @51
    @48
    @52
    @50
    @53
    @16
    @36
    @47
    vk
    vx
    cn0
    @15
    @35
    @13
    @33
    wceq
    @14
    @34
    cO
    c.as
    @13
    @33
    @6
    fveq2
    oveq1d
    cbvmptv
    #
    eleq1i
    @16
    @36
    @49
    cfsupp
    @54
    breq1i
    anbi12i
    cA
    cW
    cY
    cP
    cQ
    cR
    cT
    c.x
    vn
    c.ex
    cE
    cI
    c.xb
    cB
    @36
    cN
    cZ
    cX
    cpmidgsum.p
    cpmidgsum.y
    cpmidgsum.w
    cpmidpmat.m
    cpmidpmat.e
    cpmidpmat.z
    cpmidgsum.a
    cpmidgsum.b
    cpmidpmat.p
    cpmidpmat.i
    cpmidgsum.e
    cpmidgsum.x
    cpmidgsum.m
    cpmidgsumm2pm.t
    pm2mp
    sylan2b
    syl12anc
    @27
    @41
    cI
    @26
    @40
    cY
    cgsu
    vn
    cn0
    @25
    @39
    @24
    @38
    @5
    c.x
    @17
    @37
    cT
    @4
    @16
    @36
    @54
    fveq1i
    #
    fveq2i
    oveq2i
    mpteq2i
    oveq2i
    fveq2i
    @20
    @44
    cQ
    cgsu
    vn
    cn0
    @19
    @43
    @17
    @37
    @18
    c.xb
    @55
    oveq1i
    mpteq2i
    oveq2i
    3eqtr4g
    eqtrd
    @3
    @20
    @23
    cQ
    cgsu
    @3
    vn
    cn0
    @19
    @22
    @30
    @17
    @7
    @18
    c.xb
    @29
    @17
    @7
    wceq
    @3
    @32
    adantl
    oveq1d
    mpteq2dva
    oveq2d
    3eqtrd
end
