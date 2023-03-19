include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cmat.mm"
include "cur.mm"
include "cvsca.mm"
include "cmat2pmat.mm"
include "csg.mm"
include "cmdat.mm"
include "cmpt.mm"
include "cgsu.mm"
include "eqid.mm"
include "chpmatval.mm"
include "adantr.mm"
include "cbs.mm"
include "c0g.mm"
include "ply1crng.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "crg.mm"
include "crngring.mm"
include "3anim2i.mm"
include "chpdmatlem1.mm"
include "syl.mm"
include "3jca.mm"
include "anim1i.mm"
include "chpdmatlem2.mm"
include "sylanl1.mm"
include "exp31.mm"
include "a2d.mm"
include "ralimdva.mm"
include "imp.mm"
include "mdetdiag.mm"
include "sylc.mm"
include "chpdmatlem3.mm"
include "sylan.mm"
include "adantlr.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem chpdmat
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume chpdmat.c: |- C = ( N CharPlyMat R )
  assume chpdmat.p: |- P = ( Poly1 ` R )
  assume chpdmat.a: |- A = ( N Mat R )
  assume chpdmat.s: |- S = ( algSc ` P )
  assume chpdmat.b: |- B = ( Base ` A )
  assume chpdmat.x: |- X = ( var1 ` R )
  assume chpdmat.0: |- .0. = ( 0g ` R )
  assume chpdmat.g: |- G = ( mulGrp ` P )
  assume chpdmat.m: |- .- = ( -g ` P )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint G k
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint .0. k
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ A. i e. N A. j e. N ( i =/= j -> ( i M j ) = .0. ) ) -> ( C ` M ) = ( G gsum ( k e. N |-> ( X .- ( S ` ( k M k ) ) ) ) ) )

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
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @4
    @5
    cM
    co
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    wa
    #
    cM
    cC
    cfv
    #
    cX
    cN
    cP
    cmat
    co
    #
    cur
    cfv
    #
    @13
    cvsca
    cfv
    #
    co
    cM
    cN
    cR
    cmat2pmat
    co
    #
    cfv
    @13
    csg
    cfv
    #
    co
    #
    cN
    cP
    cmdat
    co
    #
    cfv
    #
    cG
    vk
    cN
    vk
    cv
    #
    @21
    @18
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    cN
    cX
    @21
    @21
    cM
    co
    cS
    cfv
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    @3
    @12
    @20
    wceq
    @10
    cA
    cB
    cC
    @19
    cP
    cR
    @16
    @15
    @14
    cM
    @17
    cN
    ccrg
    cX
    @13
    chpdmat.c
    chpdmat.a
    chpdmat.b
    chpdmat.p
    @13
    eqid
    #
    @19
    eqid
    #
    @17
    eqid
    #
    chpdmat.x
    @15
    eqid
    #
    @16
    eqid
    #
    @14
    eqid
    #
    chpmatval
    adantr
    @11
    cP
    ccrg
    wcel
    #
    @0
    @18
    @13
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    @6
    @4
    @5
    @18
    co
    cP
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    @20
    @24
    wceq
    @3
    @36
    @10
    @3
    @33
    @0
    @35
    @1
    @0
    @33
    @2
    cP
    cR
    chpdmat.p
    ply1crng
    3ad2ant2
    @0
    @1
    @2
    simp1
    @3
    @0
    cR
    crg
    wcel
    #
    @2
    w3a
    #
    @35
    @1
    @42
    @0
    @2
    cR
    crngring
    3anim2i
    #
    cA
    cB
    cC
    cP
    @13
    cR
    cS
    @16
    @15
    @14
    cG
    cM
    c.mi
    cN
    cX
    c.0
    @17
    chpdmat.c
    chpdmat.p
    chpdmat.a
    chpdmat.s
    chpdmat.b
    chpdmat.x
    chpdmat.0
    chpdmat.g
    chpdmat.m
    @27
    @32
    @30
    @29
    @31
    chpdmatlem1
    syl
    3jca
    adantr
    @3
    @10
    @41
    @3
    @9
    @40
    vi
    cN
    @3
    @4
    cN
    wcel
    #
    wa
    #
    @8
    @39
    vj
    cN
    @46
    @5
    cN
    wcel
    #
    wa
    #
    @6
    @7
    @38
    @48
    @6
    @7
    @38
    @48
    @43
    @45
    wa
    #
    @47
    wa
    @6
    @7
    @38
    @46
    @49
    @47
    @3
    @43
    @45
    @44
    anim1i
    anim1i
    cA
    cB
    cC
    cP
    @13
    cR
    cS
    @16
    @15
    @14
    vi
    vj
    cG
    cM
    c.mi
    cN
    cX
    c.0
    @17
    chpdmat.c
    chpdmat.p
    chpdmat.a
    chpdmat.s
    chpdmat.b
    chpdmat.x
    chpdmat.0
    chpdmat.g
    chpdmat.m
    @27
    @32
    @30
    @29
    @31
    chpdmatlem2
    sylanl1
    exp31
    a2d
    ralimdva
    ralimdva
    imp
    @13
    @34
    @19
    cP
    vi
    vj
    vk
    cG
    @18
    cN
    @37
    @28
    @27
    @34
    eqid
    chpdmat.g
    @37
    eqid
    mdetdiag
    sylc
    @11
    @23
    @26
    cG
    cgsu
    @11
    vk
    cN
    @22
    @25
    @3
    @21
    cN
    wcel
    #
    @22
    @25
    wceq
    #
    @10
    @3
    @43
    @50
    @51
    @44
    cA
    cB
    cC
    cP
    @13
    cR
    cS
    @16
    @15
    @14
    cG
    @21
    cM
    c.mi
    cN
    cX
    c.0
    @17
    chpdmat.c
    chpdmat.p
    chpdmat.a
    chpdmat.s
    chpdmat.b
    chpdmat.x
    chpdmat.0
    chpdmat.g
    chpdmat.m
    @27
    @32
    @30
    @29
    @31
    chpdmatlem3
    sylan
    adantlr
    mpteq2dva
    oveq2d
    3eqtrd
end
