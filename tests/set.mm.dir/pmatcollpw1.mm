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
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "pmatcollpw1lem2.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "oveq12.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simpl2.mm"
include "cmat.mm"
include "simplrl.mm"
include "simpl3.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "matecld.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "fmptd.mm"
include "cfsupp.mm"
include "wbr.mm"
include "pmatcollpw1lem1.mm"
include "3expb.mm"
include "gsumcl.mm"
include "ovmpt2d.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "wb.mm"
include "simp3.mm"
include "simp1.mm"
include "3ad2ant1.mm"
include "simpl12.mm"
include "matbas2d.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem pmatcollpw1
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
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> M = ( i e. N , j e. N |-> ( P gsum ( n e. NN0 |-> ( ( i ( M decompPMat n ) j ) .X. ( n .^ X ) ) ) ) ) )

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
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    cM
    co
    #
    @15
    @16
    @13
    co
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    @3
    @19
    va
    vb
    cN
    cN
    @3
    @15
    cN
    wcel
    #
    @16
    cN
    wcel
    #
    wa
    #
    wa
    #
    @17
    cP
    vn
    cn0
    @15
    @16
    @7
    co
    #
    @9
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @18
    cB
    cC
    cP
    cR
    c.xp
    vn
    c.ex
    cM
    cN
    cX
    va
    vb
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    pmatcollpw1.m
    pmatcollpw1.e
    pmatcollpw1.x
    pmatcollpw1lem2
    @24
    vi
    vj
    @15
    @16
    cN
    cN
    @12
    @28
    @13
    cP
    cbs
    cfv
    #
    @24
    @13
    eqidd
    @4
    @15
    wceq
    @5
    @16
    wceq
    wa
    #
    @12
    @28
    wceq
    @24
    @30
    @11
    @27
    cP
    cgsu
    @30
    vn
    cn0
    @10
    @26
    @30
    @8
    @25
    @9
    c.xp
    @4
    @15
    @5
    @16
    @7
    oveq12
    oveq1d
    mpteq2dv
    oveq2d
    adantl
    @3
    @21
    @22
    simprl
    @3
    @21
    @22
    simprr
    #
    @24
    cn0
    @29
    @27
    cP
    cvv
    cP
    c0g
    cfv
    #
    @29
    eqid
    #
    @32
    eqid
    #
    @3
    cP
    ccmn
    wcel
    #
    @23
    @1
    @0
    @35
    @2
    @1
    cP
    crg
    wcel
    #
    @35
    cP
    cR
    pmatcollpw1.p
    ply1ring
    #
    cP
    ringcmn
    syl
    3ad2ant2
    #
    adantr
    cn0
    cvv
    wcel
    #
    @24
    nn0ex
    a1i
    @24
    vn
    cn0
    @26
    @29
    @27
    @24
    @6
    cn0
    wcel
    #
    wa
    #
    @1
    @25
    cR
    cbs
    cfv
    #
    wcel
    @40
    @26
    @29
    wcel
    @24
    @1
    @40
    @0
    @1
    @2
    @23
    simpl2
    adantr
    #
    @41
    cN
    cR
    cmat
    co
    #
    @44
    cbs
    cfv
    #
    cR
    @15
    @16
    @42
    @7
    cN
    @44
    eqid
    #
    @42
    eqid
    #
    @45
    eqid
    #
    @3
    @21
    @22
    @40
    simplrl
    @24
    @22
    @40
    @31
    adantr
    @41
    @1
    @2
    @40
    @7
    @45
    wcel
    #
    @43
    @24
    @2
    @40
    @0
    @1
    @2
    @23
    simpl3
    adantr
    @24
    @40
    simpr
    #
    @44
    cB
    cC
    @45
    cP
    cR
    @6
    cM
    cN
    crg
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    @46
    @48
    decpmatcl
    #
    syl3anc
    matecld
    @50
    @29
    @25
    @6
    cP
    cR
    c.xp
    c.ex
    @42
    cP
    cmgp
    cfv
    #
    cX
    @47
    pmatcollpw1.p
    pmatcollpw1.x
    pmatcollpw1.m
    @52
    eqid
    #
    pmatcollpw1.e
    @33
    ply1tmcl
    syl3anc
    @27
    eqid
    fmptd
    @3
    @21
    @22
    @27
    @32
    cfsupp
    wbr
    cB
    cC
    cP
    cR
    c.xp
    vn
    c.ex
    @15
    @16
    cM
    cN
    cX
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    pmatcollpw1.m
    pmatcollpw1.e
    pmatcollpw1.x
    pmatcollpw1lem1
    3expb
    gsumcl
    ovmpt2d
    eqtr4d
    ralrimivva
    @3
    @2
    @13
    cB
    wcel
    @14
    @20
    wb
    @0
    @1
    @2
    simp3
    #
    @3
    vi
    vj
    cC
    cB
    @12
    cP
    @29
    cN
    crg
    pmatcollpw1.c
    @33
    pmatcollpw1.b
    @0
    @1
    @2
    simp1
    @1
    @0
    @36
    @2
    @37
    3ad2ant2
    @3
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
    cn0
    @29
    @11
    cP
    cvv
    @32
    @33
    @34
    @3
    @55
    @35
    @56
    @38
    3ad2ant1
    @39
    @57
    nn0ex
    a1i
    @57
    vn
    cn0
    @10
    @29
    @11
    @57
    @40
    wa
    #
    @1
    @8
    @42
    wcel
    @40
    @10
    @29
    wcel
    @0
    @1
    @2
    @55
    @56
    @40
    simpl12
    #
    @58
    @44
    @45
    cR
    @4
    @5
    @42
    @7
    cN
    @46
    @47
    @48
    @3
    @55
    @56
    @40
    simpl2
    @3
    @55
    @56
    @40
    simpl3
    @58
    @1
    @2
    @40
    @49
    @59
    @57
    @2
    @40
    @3
    @55
    @2
    @56
    @54
    3ad2ant1
    adantr
    @57
    @40
    simpr
    #
    @51
    syl3anc
    matecld
    @60
    @29
    @8
    @6
    cP
    cR
    c.xp
    c.ex
    @42
    @52
    cX
    @47
    pmatcollpw1.p
    pmatcollpw1.x
    pmatcollpw1.m
    @53
    pmatcollpw1.e
    @33
    ply1tmcl
    syl3anc
    @11
    eqid
    fmptd
    cB
    cC
    cP
    cR
    c.xp
    vn
    c.ex
    @4
    @5
    cM
    cN
    cX
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    pmatcollpw1.m
    pmatcollpw1.e
    pmatcollpw1.x
    pmatcollpw1lem1
    gsumcl
    matbas2d
    cC
    cB
    cP
    va
    vb
    cN
    cM
    @13
    pmatcollpw1.c
    pmatcollpw1.b
    eqmat
    syl2anc
    mpbird
end
