include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "cn0.mm"
include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn.mm"
include "pmatcollpw3fi.mm"
include "csn.mm"
include "wo.mm"
include "wi.mm"
include "cun.mm"
include "df-n0.mm"
include "rexeqi.mm"
include "rexun.mm"
include "bitri.mm"
include "ax-1.mm"
include "c0ex.mm"
include "oveq2.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "rexsn.mm"
include "pmatcollpw3fi1lem2.mm"
include "com12.mm"
include "sylbi.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem pmatcollpw3fi1
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
  let vs: setvar s
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cI: class I
  let vg: setvar g
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
  disjoint B s
  disjoint n s
  disjoint C n
  disjoint M s
  disjoint N s
  disjoint R s
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
  disjoint f s
  disjoint D n
  disjoint A f
  disjoint A n
  disjoint A s
  disjoint C s
  disjoint D s
  disjoint T s
  disjoint X s
  disjoint .^ s
  disjoint .* s
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
  disjoint D l
  disjoint l n
  disjoint A l
  disjoint f l
  disjoint l s
  disjoint B g
  disjoint g l
  disjoint g n
  disjoint C g
  disjoint g s
  disjoint D g
  disjoint M g
  disjoint N g
  disjoint R g
  disjoint f g
  disjoint T g
  disjoint X g
  disjoint .^ g
  disjoint .* g
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. f e. ( D ^m ( 0 ... s ) ) M = ( C gsum ( n e. ( 0 ... s ) |-> ( ( n .^ X ) .* ( T ` ( f ` n ) ) ) ) ) )

  proof
    cM
    cC
    vn
    cc0
    vs
    cv
    #
    cfz
    co
    #
    vn
    cv
    #
    cX
    c.ex
    co
    @2
    vf
    cv
    cfv
    cT
    cfv
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cD
    @1
    cmap
    co
    #
    wrex
    #
    vs
    cn0
    wrex
    #
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
    @8
    vs
    cn
    wrex
    #
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
    c.as
    cM
    cN
    cX
    vs
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpw3.a
    pmatcollpw3.d
    pmatcollpw3fi
    @9
    @11
    @8
    vs
    cc0
    csn
    #
    wrex
    #
    wo
    #
    @10
    @11
    wi
    #
    @9
    @8
    vs
    cn
    @12
    cun
    #
    wrex
    @14
    @8
    vs
    cn0
    @16
    df-n0
    rexeqi
    @8
    vs
    cn
    @12
    rexun
    bitri
    @11
    @15
    @13
    @11
    @10
    ax-1
    @13
    cM
    cC
    vn
    @12
    @3
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cD
    @12
    cmap
    co
    #
    wrex
    #
    @15
    @8
    @21
    vs
    cc0
    c0ex
    @0
    cc0
    wceq
    #
    @6
    @19
    vf
    @7
    @20
    @22
    @1
    @12
    cD
    cmap
    @22
    @1
    cc0
    cc0
    cfz
    co
    #
    @12
    @0
    cc0
    cc0
    cfz
    oveq2
    cc0
    cz
    wcel
    @23
    @12
    wceq
    @22
    0z
    cc0
    fzsn
    mp1i
    eqtrd
    #
    oveq2d
    @22
    @5
    @18
    cM
    @22
    @4
    @17
    cC
    cgsu
    @22
    vn
    @1
    @12
    @3
    @24
    mpteq1d
    oveq2d
    eqeq2d
    rexeqbidv
    rexsn
    @10
    @21
    @11
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
    c.as
    cM
    cN
    cX
    vs
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpw3.a
    pmatcollpw3.d
    pmatcollpw3fi1lem2
    com12
    sylbi
    jaoi
    sylbi
    mpcom
end
