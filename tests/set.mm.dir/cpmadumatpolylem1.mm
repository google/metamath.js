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
include "ccom.mm"
include "cn0.mm"
include "wf.mm"
include "crg.mm"
include "simp1.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "jca.mm"
include "ad2antrr.mm"
include "cpm2mf.mm"
include "syl.mm"
include "chfacfisfcpmat.mm"
include "syl3anl2.mm"
include "anassrs.mm"
include "fco.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nn0ex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem cpmadumatpolylem1
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
  assert |- ( ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ s e. NN ) /\ b e. ( B ^m ( 0 ... s ) ) ) -> ( U o. G ) e. ( B ^m NN0 ) )

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
    cU
    cG
    ccom
    #
    cB
    cn0
    cmap
    co
    wcel
    #
    cn0
    cB
    @8
    wf
    #
    @7
    cS
    cB
    cU
    wf
    #
    cn0
    cS
    cG
    wf
    #
    @10
    @7
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @11
    @3
    @14
    @5
    @6
    @3
    @0
    @13
    @0
    @1
    @2
    simp1
    @1
    @0
    @13
    @2
    cR
    crngring
    #
    3ad2ant2
    jca
    ad2antrr
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
    @3
    @5
    @6
    @12
    @1
    @0
    @13
    @2
    @5
    @6
    wa
    @12
    @15
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
    cn0
    cS
    cB
    cU
    cG
    fco
    syl2anc
    cB
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    wa
    @9
    @10
    wb
    @7
    @16
    @17
    cB
    cA
    cbs
    cfv
    cvv
    cpmadumatpoly.b
    cA
    cbs
    fvex
    eqeltri
    nn0ex
    pm3.2i
    cB
    cn0
    @8
    cvv
    cvv
    elmapg
    mp1i
    mpbird
end
