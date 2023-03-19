include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "anim2i.mm"
include "matring.mm"
include "3adant3.mm"
include "adantr.mm"
include "ovexd.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "clmod.mm"
include "csca.mm"
include "matlmod.mm"
include "ad2antrr.mm"
include "cmgp.mm"
include "cmnd.mm"
include "3ad2ant2.mm"
include "ringmgp.mm"
include "elfznn0.mm"
include "adantl.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "wb.mm"
include "wceq.mm"
include "ply1crng.mm"
include "matsca2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "simpll1.mm"
include "simplrl.mm"
include "simprr.mm"
include "anim1i.mm"
include "m2pmfzmap.mm"
include "syl31anc.mm"
include "lmodvscl.mm"
include "cfsupp.mm"
include "wbr.mm"
include "simpl1.mm"
include "simprl.mm"
include "fzfid.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsummulc2.mm"
include "casa.mm"
include "matassa.mm"
include "eleqtrrd.mm"
include "assaassr.mm"
include "syl13anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "eqtr3d.mm"

theorem cpmadugsumlemC
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let vi: setvar i
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vb: setvar b
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
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN0 /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( ( T ` M ) .X. ( Y gsum ( i e. ( 0 ... s ) |-> ( ( i .^ X ) .x. ( T ` ( b ` i ) ) ) ) ) ) = ( Y gsum ( i e. ( 0 ... s ) |-> ( ( i .^ X ) .x. ( ( T ` M ) .X. ( T ` ( b ` i ) ) ) ) ) ) )

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
    cn0
    wcel
    #
    vb
    cv
    #
    cB
    cc0
    @4
    cfz
    co
    #
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    cY
    vi
    @7
    cM
    cT
    cfv
    #
    vi
    cv
    #
    cX
    c.ex
    co
    #
    @12
    @6
    cfv
    cT
    cfv
    #
    c.x
    co
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    @11
    cY
    vi
    @7
    @15
    cmpt
    #
    cgsu
    co
    c.xp
    co
    cY
    vi
    @7
    @13
    @11
    @14
    c.xp
    co
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @10
    @7
    cY
    cbs
    cfv
    #
    cY
    cplusg
    cfv
    #
    cY
    c.xp
    vi
    cvv
    @15
    @11
    cY
    c0g
    cfv
    #
    @21
    eqid
    #
    @23
    eqid
    @22
    eqid
    cpmadugsum.r
    @3
    cY
    crg
    wcel
    #
    @9
    @0
    @1
    @25
    @2
    @0
    @1
    wa
    #
    @0
    cP
    crg
    wcel
    #
    wa
    #
    @25
    @1
    @27
    @0
    @1
    cR
    crg
    wcel
    #
    @27
    cR
    crngring
    #
    cP
    cR
    cpmadugsum.p
    ply1ring
    syl
    #
    anim2i
    #
    cY
    cP
    cN
    cpmadugsum.y
    matring
    syl
    3adant3
    adantr
    @10
    cc0
    @4
    cfz
    ovexd
    @3
    @11
    @21
    wcel
    #
    @9
    @1
    @0
    @29
    @2
    @33
    @30
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    cpmadugsum.t
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    mat2pmatbas
    syl3an2
    #
    adantr
    @10
    @12
    @7
    wcel
    #
    wa
    #
    cY
    clmod
    wcel
    #
    @13
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @14
    @21
    wcel
    #
    @15
    @21
    wcel
    @3
    @37
    @9
    @35
    @3
    @28
    @37
    @0
    @1
    @28
    @2
    @32
    3adant3
    cY
    cP
    cN
    cpmadugsum.y
    matlmod
    syl
    ad2antrr
    @36
    @40
    @13
    cP
    cbs
    cfv
    #
    wcel
    #
    @36
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @12
    cn0
    wcel
    #
    cX
    @42
    wcel
    #
    @43
    @3
    @45
    @9
    @35
    @3
    @27
    @45
    @1
    @0
    @27
    @2
    @31
    3ad2ant2
    cP
    @44
    @44
    eqid
    #
    ringmgp
    #
    syl
    ad2antrr
    @35
    @46
    @10
    @12
    @4
    elfznn0
    adantl
    #
    @3
    @47
    @9
    @35
    @3
    @29
    @47
    @1
    @0
    @29
    @2
    @30
    3ad2ant2
    #
    @42
    cP
    cR
    cX
    cpmadugsum.x
    cpmadugsum.p
    @42
    eqid
    #
    vr1cl
    syl
    ad2antrr
    #
    @42
    c.ex
    @44
    @12
    cX
    @42
    cP
    @44
    @48
    @52
    mgpbas
    cpmadugsum.e
    mulgnn0cl
    #
    syl3anc
    @3
    @40
    @43
    wb
    @9
    @35
    @3
    @39
    @42
    @13
    @3
    @38
    cP
    cbs
    @3
    cP
    @38
    @3
    @0
    cP
    ccrg
    wcel
    #
    wa
    #
    cP
    @38
    wceq
    @0
    @1
    @56
    @2
    @1
    @55
    @0
    cP
    cR
    cpmadugsum.p
    ply1crng
    anim2i
    #
    3adant3
    cY
    cP
    cN
    ccrg
    cpmadugsum.y
    matsca2
    syl
    eqcomd
    fveq2d
    #
    eleq2d
    ad2antrr
    mpbird
    @36
    @0
    @29
    @5
    @8
    @35
    wa
    @41
    @0
    @1
    @2
    @9
    @35
    simpll1
    @3
    @29
    @9
    @35
    @51
    ad2antrr
    @3
    @5
    @8
    @35
    simplrl
    @10
    @8
    @35
    @3
    @5
    @8
    simprr
    #
    anim1i
    cA
    cB
    cP
    cR
    @4
    cT
    @12
    cN
    cY
    vb
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    cpmadugsum.t
    m2pmfzmap
    syl31anc
    #
    @13
    c.x
    @38
    @39
    @21
    cY
    @14
    @24
    @38
    eqid
    #
    cpmadugsum.m
    @39
    eqid
    #
    lmodvscl
    syl3anc
    @10
    @0
    @29
    @5
    @8
    @18
    @23
    cfsupp
    wbr
    @0
    @1
    @2
    @9
    simpl1
    @3
    @29
    @9
    @51
    adantr
    @3
    @5
    @8
    simprl
    @59
    @0
    @29
    @5
    w3a
    @8
    wa
    #
    vi
    @7
    @18
    cvv
    cvv
    @15
    @23
    @18
    eqid
    @63
    cc0
    @4
    fzfid
    @63
    @35
    wa
    @13
    @14
    c.x
    ovexd
    @63
    cY
    c0g
    fvexd
    fsuppmptdm
    syl31anc
    gsummulc2
    @10
    @17
    @20
    cY
    cgsu
    @10
    vi
    @7
    @16
    @19
    @36
    cY
    casa
    wcel
    #
    @40
    @33
    @41
    @16
    @19
    wceq
    @3
    @64
    @9
    @35
    @0
    @1
    @64
    @2
    @26
    @56
    @64
    @57
    cY
    cP
    cN
    cpmadugsum.y
    matassa
    syl
    3adant3
    ad2antrr
    @36
    @13
    @42
    @39
    @36
    @45
    @46
    @47
    @43
    @3
    @45
    @9
    @35
    @0
    @1
    @45
    @2
    @26
    @27
    @45
    @1
    @27
    @0
    @31
    adantl
    @49
    syl
    3adant3
    ad2antrr
    @50
    @53
    @54
    syl3anc
    @3
    @39
    @42
    wceq
    @9
    @35
    @58
    ad2antrr
    eleqtrrd
    @3
    @33
    @9
    @35
    @34
    ad2antrr
    @60
    @13
    @39
    c.x
    c.xp
    @38
    @21
    cY
    @11
    @14
    @24
    @61
    @62
    cpmadugsum.m
    cpmadugsum.r
    assaassr
    syl13anc
    mpteq2dva
    oveq2d
    eqtr3d
end
