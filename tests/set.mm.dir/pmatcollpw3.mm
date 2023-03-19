include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cdecpmat.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "pmatcollpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "ssid.mm"
include "cc0.mm"
include "0nn0.mm"
include "ne0ii.mm"
include "pmatcollpw3lem.mm"
include "mpanr12.mm"
include "mpd.mm"

theorem pmatcollpw3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cI: class I
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )
  assume pmatcollpw3.a: |- A = ( N Mat R )
  assume pmatcollpw3.d: |- D = ( Base ` A )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint C n
  disjoint B f
  disjoint C f
  disjoint f n
  disjoint D f
  disjoint M f
  disjoint N f
  disjoint R f
  disjoint T f
  disjoint X f
  disjoint .^ f
  disjoint .* f
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i n
  disjoint j n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint .* a
  disjoint .* b
  disjoint .^ a
  disjoint .^ b
  disjoint .^ i
  disjoint .^ j
  disjoint B s
  disjoint n s
  disjoint M s
  disjoint N s
  disjoint R s
  disjoint f i
  disjoint f j
  disjoint B k
  disjoint B l
  disjoint B x
  disjoint B y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B m
  disjoint f x
  disjoint n x
  disjoint D k
  disjoint f k
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I x
  disjoint I y
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint I f
  disjoint I n
  disjoint k n
  disjoint M k
  disjoint M l
  disjoint M x
  disjoint M y
  disjoint M m
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint N k
  disjoint N l
  disjoint N x
  disjoint N y
  disjoint N m
  disjoint R k
  disjoint R l
  disjoint R x
  disjoint R y
  disjoint R m
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. f e. ( D ^m NN0 ) M = ( C gsum ( n e. NN0 |-> ( ( n .^ X ) .* ( T ` ( f ` n ) ) ) ) ) )

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
    cM
    cC
    vn
    cn0
    vn
    cv
    #
    cX
    c.ex
    co
    #
    cM
    @1
    cdecpmat
    co
    cT
    cfv
    c.as
    co
    cmpt
    cgsu
    co
    wceq
    #
    cM
    cC
    vn
    cn0
    @2
    @1
    vf
    cv
    cfv
    cT
    cfv
    c.as
    co
    cmpt
    cgsu
    co
    wceq
    vf
    cD
    cn0
    cmap
    co
    wrex
    #
    cB
    cC
    cP
    cR
    cT
    vn
    c.ex
    c.as
    cM
    cN
    cX
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpw
    @0
    cn0
    cn0
    wss
    cn0
    c0
    wne
    @3
    @4
    wi
    cn0
    ssid
    cc0
    cn0
    0nn0
    ne0ii
    cA
    cB
    cC
    cD
    cP
    cR
    cT
    vf
    vn
    c.ex
    cn0
    c.as
    cM
    cN
    cX
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpw3.a
    pmatcollpw3.d
    pmatcollpw3lem
    mpanr12
    mpd
end
