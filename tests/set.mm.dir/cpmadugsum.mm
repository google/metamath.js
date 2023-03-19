include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "cn0.mm"
include "cpmadugsumfi.mm"
include "wa.mm"
include "simpr.mm"
include "chfacfscmulgsum.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "reximdvva.mm"
include "mpd.mm"

theorem cpmadugsum
  let cA: class A
  let cB: class B
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
  let cI: class I
  let cJ: class J
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
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) ( I .X. ( J ` I ) ) = ( Y gsum ( i e. NN0 |-> ( ( i .^ X ) .x. ( G ` i ) ) ) ) )

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
    cI
    cI
    cJ
    cfv
    c.xp
    co
    #
    cY
    vi
    c1
    vs
    cv
    #
    cfz
    co
    vi
    cv
    #
    cX
    c.ex
    co
    #
    @3
    c1
    cmin
    co
    vb
    cv
    #
    cfv
    cT
    cfv
    cM
    cT
    cfv
    #
    @3
    @5
    cfv
    cT
    cfv
    c.xp
    co
    c.mi
    co
    c.x
    co
    cmpt
    cgsu
    co
    @2
    c1
    caddc
    co
    cX
    c.ex
    co
    @2
    @5
    cfv
    cT
    cfv
    c.x
    co
    @6
    cc0
    @5
    cfv
    cT
    cfv
    c.xp
    co
    c.mi
    co
    c.pl
    co
    #
    wceq
    #
    vb
    cB
    cc0
    @2
    cfz
    co
    cmap
    co
    #
    wrex
    vs
    cn
    wrex
    @1
    cY
    vi
    cn0
    @4
    @3
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
    @9
    wrex
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
    c.ex
    cI
    cJ
    cM
    c.mi
    cN
    cX
    cY
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
    cpmadugsumfi
    @0
    @8
    @11
    vs
    vb
    cn
    @9
    @0
    @2
    cn
    wcel
    @5
    @9
    wcel
    wa
    wa
    #
    @8
    @11
    @12
    @8
    wa
    @1
    @7
    @10
    @12
    @8
    simpr
    @12
    @7
    @10
    wceq
    @8
    @12
    @10
    @7
    cA
    cB
    cP
    c.pl
    cR
    cT
    c.x
    c.xp
    vi
    vn
    c.ex
    cG
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
    cpmadugsum.r
    cpmadugsum.s
    cpmadugsum.0
    cpmadugsum.t
    cpmadugsum.g2
    cpmadugsum.x
    cpmadugsum.m
    cpmadugsum.e
    cpmadugsum.g
    chfacfscmulgsum
    eqcomd
    adantr
    eqtrd
    ex
    reximdvva
    mpd
end
