include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "co.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cco1.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wa.mm"
include "eqid.mm"
include "cpmidgsum.mm"
include "eqcomd.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "eqtrd.mm"
include "cpmidgsum2.mm"
include "reximddv2.mm"

theorem cpmidg2sum
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vi: setvar i
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
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
  assume cpmidg2sum.u: |- U = ( algSc ` P )

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
  disjoint A i
  disjoint K i
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
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) ( Y gsum ( i e. NN0 |-> ( ( i .^ X ) .x. ( ( U ` ( ( coe1 ` K ) ` i ) ) .x. .1. ) ) ) ) = ( Y gsum ( i e. NN0 |-> ( ( i .^ X ) .x. ( G ` i ) ) ) ) )

  proof
    cN
    cfn
    wcel
    cR
    ccrg
    wcel
    cM
    cB
    wcel
    w3a
    #
    cK
    c.1
    c.x
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
    #
    @2
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
    cY
    vi
    cn0
    @3
    @2
    cK
    cco1
    cfv
    cfv
    cU
    cfv
    c.1
    c.x
    co
    c.x
    co
    cmpt
    cgsu
    co
    #
    @4
    wceq
    vs
    vb
    cn
    cB
    cc0
    vs
    cv
    #
    cfz
    co
    cmap
    co
    #
    @0
    @7
    cn
    wcel
    #
    wa
    vb
    cv
    @8
    wcel
    #
    wa
    #
    @5
    wa
    @6
    @1
    @4
    @0
    @6
    @1
    wceq
    @9
    @10
    @5
    @0
    @1
    @6
    cA
    cB
    cC
    cP
    cR
    c.x
    cU
    c.1
    vi
    c.ex
    @1
    cK
    cM
    cN
    cX
    cY
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    cpmadugsum.x
    cpmadugsum.e
    cpmadugsum.m
    cpmadugsum.1
    cpmidg2sum.u
    cpmidgsum2.c
    cpmidgsum2.k
    @1
    eqid
    #
    cpmidgsum
    eqcomd
    ad3antrrr
    @11
    @5
    simpr
    eqtrd
    cA
    cB
    cC
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
    @1
    cI
    cJ
    cK
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
    cpmidgsum2.c
    cpmidgsum2.k
    @12
    cpmidgsum2
    reximddv2
end
