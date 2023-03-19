include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cn0.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "fvexd.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "0elcpmat.mm"
include "syl.mm"
include "wf.mm"
include "chfacfisfcpmat.mm"
include "syl3anl2.mm"
include "anassrs.mm"
include "cpm2mf.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "nn0ex.mm"
include "ccpmat.mm"
include "ovex.mm"
include "eqeltri.mm"
include "cfsupp.mm"
include "wbr.mm"
include "chfacffsupp.mm"
include "wceq.mm"
include "eqid.mm"
include "m2cpminv0.mm"
include "sylan2.mm"
include "fsuppcor.mm"

theorem cpmadumatpolylem2
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let c.as: class .*
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vb: setvar b
  assume cpmadumatpoly.a: |- A = ( N Mat R )
  assume cpmadumatpoly.b: |- B = ( Base ` A )
  assume cpmadumatpoly.p: |- P = ( Poly1 ` R )
  assume cpmadumatpoly.y: |- Y = ( N Mat P )
  assume cpmadumatpoly.t: |- T = ( N matToPolyMat R )
  assume cpmadumatpoly.r: |- .X. = ( .r ` Y )
  assume cpmadumatpoly.m0: |- .- = ( -g ` Y )
  assume cpmadumatpoly.0: |- .0. = ( 0g ` Y )
  assume cpmadumatpoly.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cpmadumatpoly.s: |- S = ( N ConstPolyMat R )
  assume cpmadumatpoly.m1: |- .x. = ( .s ` Y )
  assume cpmadumatpoly.1: |- .1. = ( 1r ` Y )
  assume cpmadumatpoly.z: |- Z = ( var1 ` R )
  assume cpmadumatpoly.d: |- D = ( ( Z .x. .1. ) .- ( T ` M ) )
  assume cpmadumatpoly.j: |- J = ( N maAdju P )
  assume cpmadumatpoly.w: |- W = ( Base ` Y )
  assume cpmadumatpoly.q: |- Q = ( Poly1 ` A )
  assume cpmadumatpoly.x: |- X = ( var1 ` A )
  assume cpmadumatpoly.m2: |- .* = ( .s ` Q )
  assume cpmadumatpoly.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume cpmadumatpoly.u: |- U = ( N cPolyMatToMat R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint S n
  disjoint Y n
  disjoint b n
  disjoint n s
  assert |- ( ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ s e. NN ) /\ b e. ( B ^m ( 0 ... s ) ) ) -> ( U o. G ) finSupp ( 0g ` A ) )

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
    vs
    cv
    #
    cn
    wcel
    #
    wa
    vb
    cv
    cB
    cc0
    @4
    cfz
    co
    cmap
    co
    wcel
    #
    wa
    #
    cn0
    cS
    cS
    cB
    cvv
    cG
    cU
    cvv
    cvv
    cA
    c0g
    cfv
    #
    cY
    c0g
    cfv
    #
    @7
    cA
    c0g
    fvexd
    @7
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @9
    cS
    wcel
    @3
    @11
    @5
    @6
    @0
    @1
    @11
    @2
    @1
    @10
    @0
    cR
    crngring
    #
    anim2i
    3adant3
    ad2antrr
    #
    cY
    cP
    cR
    cS
    cN
    cpmadumatpoly.s
    cpmadumatpoly.p
    cpmadumatpoly.y
    0elcpmat
    syl
    @3
    @5
    @6
    cn0
    cS
    cG
    wf
    #
    @1
    @0
    @10
    @2
    @5
    @6
    wa
    @14
    @12
    cA
    cB
    cP
    cR
    cS
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.r
    cpmadumatpoly.m0
    cpmadumatpoly.0
    cpmadumatpoly.t
    cpmadumatpoly.g
    cpmadumatpoly.s
    chfacfisfcpmat
    syl3anl2
    anassrs
    @7
    @11
    cS
    cB
    cU
    wf
    @13
    cA
    cR
    cS
    cU
    cB
    cN
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.s
    cpmadumatpoly.u
    cpm2mf
    syl
    cS
    cS
    wss
    @7
    cS
    ssid
    a1i
    cn0
    cvv
    wcel
    @7
    nn0ex
    a1i
    cS
    cvv
    wcel
    @7
    cS
    cN
    cR
    ccpmat
    co
    cvv
    cpmadumatpoly.s
    cN
    cR
    ccpmat
    ovex
    eqeltri
    a1i
    @3
    @5
    @6
    cG
    @9
    cfsupp
    wbr
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    cpmadumatpoly.a
    cpmadumatpoly.b
    cpmadumatpoly.p
    cpmadumatpoly.y
    cpmadumatpoly.r
    cpmadumatpoly.m0
    cpmadumatpoly.0
    cpmadumatpoly.t
    cpmadumatpoly.g
    chfacffsupp
    anassrs
    @3
    @9
    cU
    cfv
    @8
    wceq
    #
    @5
    @6
    @0
    @1
    @15
    @2
    @1
    @0
    @10
    @15
    @12
    cA
    cY
    cP
    cR
    cU
    cN
    @8
    @9
    cpmadumatpoly.a
    cpmadumatpoly.u
    cpmadumatpoly.p
    cpmadumatpoly.y
    @8
    eqid
    @9
    eqid
    m2cpminv0
    sylan2
    3adant3
    ad2antrr
    fsuppcor
end
