include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "pmatcollpw1.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "simp1.mm"
include "nn0ex.mm"
include "a1i.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "cbs.mm"
include "adantr.mm"
include "simp1l2.mm"
include "cmat.mm"
include "simp2.mm"
include "simp3.mm"
include "simpr.mm"
include "3jca.mm"
include "3ad2ant1.mm"
include "decpmatcl.mm"
include "syl.mm"
include "matecld.mm"
include "simp1r.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "matbas2d.mm"
include "pmatcollpw2lem.mm"
include "matgsum.mm"
include "eqtr4d.mm"

theorem pmatcollpw2
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  assume pmatcollpw1.p: |- P = ( Poly1 ` R )
  assume pmatcollpw1.c: |- C = ( N Mat P )
  assume pmatcollpw1.b: |- B = ( Base ` C )
  assume pmatcollpw1.m: |- .X. = ( .s ` P )
  assume pmatcollpw1.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw1.x: |- X = ( var1 ` R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint X n
  disjoint .X. n
  disjoint .^ n
  disjoint P n
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint i n
  disjoint j n
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint .X. i
  disjoint .X. j
  disjoint .^ i
  disjoint .^ j
  disjoint B s
  disjoint B x
  disjoint n s
  disjoint n x
  disjoint s x
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint M s
  disjoint M x
  disjoint N s
  disjoint N x
  disjoint P s
  disjoint P x
  disjoint R s
  disjoint R x
  disjoint X s
  disjoint X x
  disjoint .X. s
  disjoint .X. x
  disjoint .^ s
  disjoint .^ x
  disjoint a n
  disjoint b n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint X a
  disjoint X b
  disjoint .X. a
  disjoint .X. b
  disjoint .^ a
  disjoint .^ b
  disjoint B y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint n y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint M y
  disjoint N y
  disjoint R y
  disjoint X y
  disjoint .X. y
  disjoint .^ y
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> M = ( C gsum ( n e. NN0 |-> ( i e. N , j e. N |-> ( ( i ( M decompPMat n ) j ) .X. ( n .^ X ) ) ) ) ) )

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
    cM
    vi
    vj
    cN
    cN
    cP
    vn
    cn0
    vi
    cv
    #
    vj
    cv
    #
    cM
    vn
    cv
    #
    cdecpmat
    co
    #
    co
    #
    @6
    cX
    c.ex
    co
    c.xp
    co
    #
    cmpt
    cgsu
    co
    cmpt2
    cC
    vn
    cn0
    vi
    vj
    cN
    cN
    @9
    cmpt2
    cmpt
    cgsu
    co
    cB
    cC
    cP
    cR
    c.xp
    vi
    vj
    vn
    c.ex
    cM
    cN
    cX
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    pmatcollpw1.m
    pmatcollpw1.e
    pmatcollpw1.x
    pmatcollpw1
    @3
    vn
    cC
    cB
    cP
    @9
    vi
    vj
    cn0
    cN
    cvv
    cC
    c0g
    cfv
    #
    pmatcollpw1.c
    pmatcollpw1.b
    @10
    eqid
    @0
    @1
    @2
    simp1
    #
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @1
    @0
    cP
    crg
    wcel
    #
    @2
    cP
    cR
    pmatcollpw1.p
    ply1ring
    3ad2ant2
    #
    @3
    @6
    cn0
    wcel
    #
    wa
    #
    vi
    vj
    cC
    cB
    @9
    cP
    cP
    cbs
    cfv
    #
    cN
    crg
    pmatcollpw1.c
    @16
    eqid
    #
    pmatcollpw1.b
    @3
    @0
    @14
    @11
    adantr
    @3
    @12
    @14
    @13
    adantr
    @15
    @4
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    w3a
    #
    @1
    @8
    cR
    cbs
    cfv
    #
    wcel
    @14
    @9
    @16
    wcel
    @0
    @1
    @2
    @14
    @18
    @19
    simp1l2
    @20
    cN
    cR
    cmat
    co
    #
    @22
    cbs
    cfv
    #
    cR
    @4
    @5
    @21
    @7
    cN
    @22
    eqid
    #
    @21
    eqid
    #
    @23
    eqid
    #
    @15
    @18
    @19
    simp2
    @15
    @18
    @19
    simp3
    @20
    @1
    @2
    @14
    w3a
    #
    @7
    @23
    wcel
    @15
    @18
    @27
    @19
    @15
    @1
    @2
    @14
    @3
    @1
    @14
    @0
    @1
    @2
    simp2
    adantr
    @3
    @2
    @14
    @0
    @1
    @2
    simp3
    adantr
    @3
    @14
    simpr
    3jca
    3ad2ant1
    @22
    cB
    cC
    @23
    cP
    cR
    @6
    cM
    cN
    crg
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    @24
    @26
    decpmatcl
    syl
    matecld
    @3
    @14
    @18
    @19
    simp1r
    @16
    @8
    @6
    cP
    cR
    c.xp
    c.ex
    @21
    cP
    cmgp
    cfv
    #
    cX
    @25
    pmatcollpw1.p
    pmatcollpw1.x
    pmatcollpw1.m
    @28
    eqid
    pmatcollpw1.e
    @17
    ply1tmcl
    syl3anc
    matbas2d
    cB
    cC
    cP
    cR
    c.xp
    vi
    vj
    vn
    c.ex
    cM
    cN
    cX
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    pmatcollpw1.m
    pmatcollpw1.e
    pmatcollpw1.x
    pmatcollpw2lem
    matgsum
    eqtr4d
end
