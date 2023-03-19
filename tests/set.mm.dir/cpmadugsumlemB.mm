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
include "c1.mm"
include "caddc.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cmulr.mm"
include "cmgp.mm"
include "cmnd.mm"
include "cbs.mm"
include "wceq.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "ringmgp.mm"
include "ad2antrr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "1nn0.mm"
include "a1i.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mulgnn0dir.mm"
include "syl13anc.mm"
include "ply1crng.mm"
include "anim2i.mm"
include "3adant3.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "mulg1.mm"
include "oveq123d.mm"
include "eqtrd.mm"
include "matring.mm"
include "simpll1.mm"
include "simplrl.mm"
include "simprr.mm"
include "anim1i.mm"
include "m2pmfzmap.mm"
include "syl31anc.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "casa.mm"
include "matassa.mm"
include "eleqtrrd.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "ringidcl.mm"
include "assa2ass.mm"
include "syl122anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cplusg.mm"
include "cvv.mm"
include "c0g.mm"
include "adantr.mm"
include "ovexd.mm"
include "clmod.mm"
include "matlmod.mm"
include "lmodvscl.mm"
include "wb.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "cfsupp.mm"
include "wbr.mm"
include "simpl1.mm"
include "simprl.mm"
include "fzfid.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "gsummulc2.mm"
include "eqtr2d.mm"

theorem cpmadugsumlemB
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
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN0 /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( ( X .x. .1. ) .X. ( Y gsum ( i e. ( 0 ... s ) |-> ( ( i .^ X ) .x. ( T ` ( b ` i ) ) ) ) ) ) = ( Y gsum ( i e. ( 0 ... s ) |-> ( ( ( i + 1 ) .^ X ) .x. ( T ` ( b ` i ) ) ) ) ) )

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
    vi
    cv
    #
    c1
    caddc
    co
    cX
    c.ex
    co
    #
    @11
    @6
    cfv
    cT
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cY
    vi
    @7
    cX
    c.1
    c.x
    co
    #
    @11
    cX
    c.ex
    co
    #
    @13
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
    @16
    cY
    vi
    @7
    @18
    cmpt
    #
    cgsu
    co
    c.xp
    co
    @10
    @15
    @20
    cY
    cgsu
    @10
    vi
    @7
    @14
    @19
    @10
    @11
    @7
    wcel
    #
    wa
    #
    @14
    @17
    cX
    cY
    csca
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    c.1
    @13
    c.xp
    co
    #
    c.x
    co
    #
    @19
    @23
    @12
    @26
    @13
    @27
    c.x
    @23
    @12
    @17
    c1
    cX
    c.ex
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    @26
    @23
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @11
    cn0
    wcel
    #
    c1
    cn0
    wcel
    #
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    @12
    @31
    wceq
    @3
    @33
    @9
    @22
    @3
    cP
    crg
    wcel
    #
    @33
    @1
    @0
    @38
    @2
    @1
    cR
    crg
    wcel
    #
    @38
    cR
    crngring
    #
    cP
    cR
    cpmadugsum.p
    ply1ring
    syl
    #
    3ad2ant2
    cP
    @32
    @32
    eqid
    #
    ringmgp
    syl
    ad2antrr
    #
    @22
    @34
    @10
    @11
    @4
    elfznn0
    adantl
    #
    @35
    @23
    1nn0
    a1i
    @3
    @37
    @9
    @22
    @3
    @39
    @37
    @1
    @0
    @39
    @2
    @40
    3ad2ant2
    #
    @36
    cP
    cR
    cX
    cpmadugsum.x
    cpmadugsum.p
    @36
    eqid
    #
    vr1cl
    #
    syl
    #
    ad2antrr
    #
    @36
    @30
    c.ex
    @32
    @11
    c1
    cX
    @36
    cP
    @32
    @42
    @46
    mgpbas
    #
    cpmadugsum.e
    cP
    @30
    @32
    @42
    @30
    eqid
    mgpplusg
    mulgnn0dir
    syl13anc
    @23
    @17
    @17
    @29
    cX
    @30
    @25
    @23
    cP
    @24
    cmulr
    @3
    cP
    @24
    wceq
    #
    @9
    @22
    @3
    @0
    cP
    ccrg
    wcel
    #
    wa
    #
    @51
    @0
    @1
    @53
    @2
    @1
    @52
    @0
    cP
    cR
    cpmadugsum.p
    ply1crng
    anim2i
    #
    3adant3
    #
    cY
    cP
    cN
    ccrg
    cpmadugsum.y
    matsca2
    #
    syl
    #
    ad2antrr
    fveq2d
    @23
    @17
    eqidd
    @3
    @29
    cX
    wceq
    #
    @9
    @22
    @3
    @37
    @58
    @48
    @36
    c.ex
    @32
    cX
    @50
    cpmadugsum.e
    mulg1
    syl
    ad2antrr
    oveq123d
    eqtrd
    @23
    @27
    @13
    @23
    cY
    crg
    wcel
    #
    @13
    cY
    cbs
    cfv
    #
    wcel
    #
    @27
    @13
    wceq
    @3
    @59
    @9
    @22
    @3
    @0
    @38
    wa
    #
    @59
    @0
    @1
    @62
    @2
    @1
    @38
    @0
    @41
    anim2i
    #
    3adant3
    cY
    cP
    cN
    cpmadugsum.y
    matring
    #
    syl
    #
    ad2antrr
    @23
    @0
    @39
    @5
    @8
    @22
    wa
    @61
    @0
    @1
    @2
    @9
    @22
    simpll1
    @3
    @39
    @9
    @22
    @45
    ad2antrr
    @3
    @5
    @8
    @22
    simplrl
    @10
    @8
    @22
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
    @11
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
    @60
    cY
    c.xp
    c.1
    @13
    @60
    eqid
    #
    cpmadugsum.r
    cpmadugsum.1
    ringlidm
    syl2anc
    eqcomd
    oveq12d
    @23
    @19
    @28
    @23
    cY
    casa
    wcel
    #
    cX
    @24
    cbs
    cfv
    #
    wcel
    #
    @17
    @70
    wcel
    #
    c.1
    @60
    wcel
    #
    @61
    @19
    @28
    wceq
    @3
    @69
    @9
    @22
    @0
    @1
    @69
    @2
    @0
    @1
    wa
    #
    @53
    @69
    @54
    cY
    cP
    cN
    cpmadugsum.y
    matassa
    syl
    3adant3
    ad2antrr
    @3
    @71
    @9
    @22
    @3
    cX
    @36
    @70
    @48
    @3
    @24
    cP
    cbs
    @3
    cP
    @24
    @57
    eqcomd
    fveq2d
    #
    eleqtrrd
    ad2antrr
    @23
    @17
    @36
    @70
    @23
    @33
    @34
    @37
    @17
    @36
    wcel
    #
    @43
    @44
    @49
    @36
    c.ex
    @32
    @11
    cX
    @50
    cpmadugsum.e
    mulgnn0cl
    syl3anc
    #
    @3
    @70
    @36
    wceq
    #
    @9
    @22
    @75
    ad2antrr
    eleqtrrd
    @3
    @73
    @9
    @22
    @3
    @59
    @73
    @0
    @1
    @59
    @2
    @74
    @62
    @59
    @63
    @64
    syl
    3adant3
    #
    @60
    cY
    c.1
    @68
    cpmadugsum.1
    ringidcl
    #
    syl
    ad2antrr
    @67
    cX
    @70
    @17
    c.x
    c.xp
    @24
    @25
    @60
    cY
    c.1
    @13
    @68
    @24
    eqid
    #
    @70
    eqid
    #
    @25
    eqid
    cpmadugsum.m
    cpmadugsum.r
    assa2ass
    syl122anc
    eqcomd
    eqtrd
    mpteq2dva
    oveq2d
    @10
    @7
    @60
    cY
    cplusg
    cfv
    #
    cY
    c.xp
    vi
    cvv
    @18
    @16
    cY
    c0g
    cfv
    #
    @68
    @84
    eqid
    @83
    eqid
    cpmadugsum.r
    @3
    @59
    @9
    @79
    adantr
    @10
    cc0
    @4
    cfz
    ovexd
    @3
    @16
    @60
    wcel
    #
    @9
    @3
    cY
    clmod
    wcel
    #
    @71
    @73
    @85
    @0
    @1
    @86
    @2
    @74
    @62
    @86
    @63
    cY
    cP
    cN
    cpmadugsum.y
    matlmod
    syl
    3adant3
    #
    @0
    @1
    @71
    @2
    @74
    cX
    @36
    @70
    @74
    @39
    @37
    @1
    @39
    @0
    @40
    adantl
    @47
    syl
    @74
    @24
    cP
    cbs
    @74
    cP
    @24
    @74
    @53
    @51
    @54
    @56
    syl
    eqcomd
    fveq2d
    eleqtrrd
    3adant3
    @3
    @59
    @73
    @65
    @80
    syl
    cX
    c.x
    @24
    @70
    @60
    cY
    c.1
    @68
    @81
    cpmadugsum.m
    @82
    lmodvscl
    syl3anc
    adantr
    @23
    @86
    @72
    @61
    @18
    @60
    wcel
    @3
    @86
    @9
    @22
    @87
    ad2antrr
    @23
    @72
    @76
    @77
    @3
    @72
    @76
    wb
    @9
    @22
    @3
    @70
    @36
    @17
    @3
    @53
    @78
    @55
    @53
    @24
    cP
    cbs
    @53
    cP
    @24
    @56
    eqcomd
    fveq2d
    syl
    eleq2d
    ad2antrr
    mpbird
    @67
    @17
    c.x
    @24
    @70
    @60
    cY
    @13
    @68
    @81
    cpmadugsum.m
    @82
    lmodvscl
    syl3anc
    @10
    @0
    @39
    @5
    @8
    @21
    @84
    cfsupp
    wbr
    @0
    @1
    @2
    @9
    simpl1
    @3
    @39
    @9
    @45
    adantr
    @3
    @5
    @8
    simprl
    @66
    @0
    @39
    @5
    w3a
    @8
    wa
    #
    vi
    @7
    @21
    cvv
    cvv
    @18
    @84
    @21
    eqid
    @88
    cc0
    @4
    fzfid
    @88
    @22
    wa
    @17
    @13
    c.x
    ovexd
    @88
    cY
    c0g
    fvexd
    fsuppmptdm
    syl31anc
    gsummulc2
    eqtr2d
end
