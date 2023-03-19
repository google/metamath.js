include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cn.mm"
include "cmap.mm"
include "wa.mm"
include "oveq2.mm"
include "a1i.mm"
include "oveq1d.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "pmatring.mm"
include "syl.mm"
include "clmod.mm"
include "csca.mm"
include "pmatlmod.mm"
include "sylan2.mm"
include "adantl.mm"
include "vr1cl.mm"
include "ply1crng.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "ringidcl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "fzfid.mm"
include "cn0.mm"
include "ad3antrrr.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "imp.mm"
include "elfznn0.mm"
include "mat2pmatscmxcl.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "rngsubdir.mm"
include "weq.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "oveq12i.mm"
include "cpmadugsumlemF.mm"
include "anassrs.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "sylan9eqr.mm"
include "wrex.mm"
include "maduf.mm"
include "3ad2ant2.mm"
include "chmatcl.mm"
include "ffvelrnd.mm"
include "pmatcollpw3fi1.mm"
include "syld3an3.mm"
include "reximddv2.mm"

theorem cpmadugsumfi
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
  let c.ex: class .^
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vb: setvar b
  let vx: setvar x
  let vn: setvar n
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
  disjoint A s
  disjoint b s
  disjoint B b
  disjoint B s
  disjoint I b
  disjoint I i
  disjoint I s
  disjoint J b
  disjoint J i
  disjoint J s
  disjoint M b
  disjoint M s
  disjoint N b
  disjoint N s
  disjoint P i
  disjoint R b
  disjoint R s
  disjoint T b
  disjoint T s
  disjoint X b
  disjoint X s
  disjoint Y b
  disjoint Y s
  disjoint .^ s
  disjoint .^ b
  disjoint .x. b
  disjoint .x. s
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
  disjoint A n
  disjoint b n
  disjoint n s
  disjoint B n
  disjoint I n
  disjoint i n
  disjoint J n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint T n
  disjoint X n
  disjoint Y n
  disjoint .^ n
  disjoint .x. n
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) ( I .X. ( J ` I ) ) = ( ( Y gsum ( i e. ( 1 ... s ) |-> ( ( i .^ X ) .x. ( ( T ` ( b ` ( i - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` i ) ) ) ) ) ) ) .+ ( ( ( ( s + 1 ) .^ X ) .x. ( T ` ( b ` s ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) ) )

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
    cI
    cJ
    cfv
    #
    cY
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
    #
    @7
    vb
    cv
    #
    cfv
    #
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
    #
    wceq
    #
    cI
    @4
    c.xp
    co
    #
    cY
    vi
    c1
    @5
    cfz
    co
    vi
    cv
    #
    cX
    c.ex
    co
    #
    @17
    c1
    cmin
    co
    @9
    cfv
    cT
    cfv
    cM
    cT
    cfv
    #
    @17
    @9
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    c.mi
    co
    c.x
    co
    cmpt
    cgsu
    co
    @5
    c1
    caddc
    co
    cX
    c.ex
    co
    @5
    @9
    cfv
    cT
    cfv
    c.x
    co
    @19
    cc0
    @9
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
    vs
    vb
    cn
    cB
    @6
    cmap
    co
    #
    @15
    @3
    @5
    cn
    wcel
    #
    wa
    #
    @9
    @23
    wcel
    #
    wa
    #
    @16
    cI
    @14
    c.xp
    co
    #
    @22
    @4
    @14
    cI
    c.xp
    oveq2
    @27
    @28
    cX
    c.1
    c.x
    co
    #
    @19
    c.mi
    co
    #
    @14
    c.xp
    co
    @29
    @14
    c.xp
    co
    #
    @19
    @14
    c.xp
    co
    #
    c.mi
    co
    #
    @22
    @27
    cI
    @30
    @14
    c.xp
    cI
    @30
    wceq
    @27
    cpmadugsum.i
    a1i
    oveq1d
    @27
    cY
    cbs
    cfv
    #
    cY
    c.xp
    c.mi
    @29
    @19
    @14
    @34
    eqid
    #
    cpmadugsum.r
    cpmadugsum.s
    @27
    @0
    cR
    crg
    wcel
    #
    wa
    #
    cY
    crg
    wcel
    #
    @3
    @37
    @24
    @26
    @0
    @1
    @37
    @2
    @1
    @36
    @0
    cR
    crngring
    #
    anim2i
    3adant3
    #
    ad2antrr
    cY
    cP
    cR
    cN
    cpmadugsum.p
    cpmadugsum.y
    pmatring
    #
    syl
    @3
    @29
    @34
    wcel
    #
    @24
    @26
    @0
    @1
    @42
    @2
    @0
    @1
    wa
    #
    cY
    clmod
    wcel
    #
    cX
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    c.1
    @34
    wcel
    #
    @42
    @1
    @0
    @36
    @44
    @39
    cY
    cP
    cR
    cN
    cpmadugsum.p
    cpmadugsum.y
    pmatlmod
    sylan2
    @43
    cX
    cP
    cbs
    cfv
    #
    @46
    @43
    @36
    cX
    @48
    wcel
    @1
    @36
    @0
    @39
    adantl
    @48
    cP
    cR
    cX
    cpmadugsum.x
    cpmadugsum.p
    @48
    eqid
    vr1cl
    syl
    @43
    cP
    @45
    cbs
    @1
    @0
    cP
    ccrg
    wcel
    #
    cP
    @45
    wceq
    cP
    cR
    cpmadugsum.p
    ply1crng
    #
    cY
    cP
    cN
    ccrg
    cpmadugsum.y
    matsca2
    sylan2
    fveq2d
    eleqtrd
    @43
    @38
    @47
    @1
    @0
    @36
    @38
    @39
    @41
    sylan2
    #
    @34
    cY
    c.1
    @35
    cpmadugsum.1
    ringidcl
    syl
    cX
    c.x
    @45
    @46
    @34
    cY
    c.1
    @35
    @45
    eqid
    cpmadugsum.m
    @46
    eqid
    lmodvscl
    syl3anc
    3adant3
    ad2antrr
    @3
    @19
    @34
    wcel
    #
    @24
    @26
    @1
    @0
    @36
    @2
    @52
    @39
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
    ad2antrr
    @27
    @34
    vn
    cY
    @6
    @12
    @35
    @3
    cY
    ccmn
    wcel
    #
    @24
    @26
    @0
    @1
    @53
    @2
    @43
    @38
    @53
    @51
    cY
    ringcmn
    syl
    3adant3
    ad2antrr
    @27
    cc0
    @5
    fzfid
    @27
    @12
    @34
    wcel
    #
    vn
    @6
    @27
    @7
    @6
    wcel
    #
    wa
    @37
    @10
    cB
    wcel
    #
    @7
    cn0
    wcel
    #
    @54
    @3
    @37
    @24
    @26
    @55
    @40
    ad3antrrr
    @27
    @55
    @56
    @26
    @55
    @56
    wi
    #
    @25
    @26
    @6
    cB
    @9
    wf
    #
    @58
    @9
    cB
    @6
    elmapi
    @59
    @55
    @56
    @6
    cB
    @7
    @9
    ffvelrn
    ex
    syl
    adantl
    imp
    @55
    @57
    @27
    @7
    @5
    elfznn0
    adantl
    cA
    @34
    cY
    cP
    cR
    cT
    c.ex
    c.x
    cB
    @7
    @10
    cN
    cX
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.t
    cpmadugsum.p
    cpmadugsum.y
    @35
    cpmadugsum.m
    cpmadugsum.e
    cpmadugsum.x
    mat2pmatscmxcl
    syl12anc
    ralrimiva
    gsummptcl
    rngsubdir
    @27
    @33
    @29
    cY
    vi
    @6
    @18
    @21
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.xp
    co
    #
    @19
    @62
    c.xp
    co
    #
    c.mi
    co
    #
    @22
    @31
    @63
    @32
    @64
    c.mi
    @14
    @62
    @29
    c.xp
    @13
    @61
    cY
    cgsu
    vn
    vi
    @6
    @12
    @60
    vn
    vi
    weq
    #
    @8
    @18
    @11
    @21
    c.x
    @7
    @17
    cX
    c.ex
    oveq1
    @66
    @10
    @20
    cT
    @7
    @17
    @9
    fveq2
    fveq2d
    oveq12d
    cbvmptv
    oveq2i
    #
    oveq2i
    @14
    @62
    @19
    c.xp
    @67
    oveq2i
    oveq12i
    @3
    @24
    @26
    @65
    @22
    wceq
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
    cpmadugsumlemF
    anassrs
    syl5eq
    3eqtrd
    sylan9eqr
    @0
    @1
    @2
    @4
    @34
    wcel
    @15
    vb
    @23
    wrex
    vs
    cn
    wrex
    @3
    @34
    @34
    cI
    cJ
    @1
    @0
    @34
    @34
    cJ
    wf
    #
    @2
    @1
    @49
    @68
    @50
    cY
    @34
    cP
    cJ
    cN
    cpmadugsum.y
    cpmadugsum.j
    @35
    maduf
    syl
    3ad2ant2
    @1
    @0
    @36
    @2
    cI
    @34
    wcel
    @39
    cA
    cB
    cP
    cR
    cT
    c.x
    c.1
    cI
    cM
    c.mi
    cN
    cX
    cY
    cpmadugsum.a
    cpmadugsum.b
    cpmadugsum.p
    cpmadugsum.y
    cpmadugsum.x
    cpmadugsum.t
    cpmadugsum.s
    cpmadugsum.m
    cpmadugsum.1
    cpmadugsum.i
    chmatcl
    syl3an2
    ffvelrnd
    cA
    @34
    cY
    cB
    cP
    cR
    cT
    vb
    vn
    c.ex
    c.x
    @4
    cN
    cX
    vs
    cpmadugsum.p
    cpmadugsum.y
    @35
    cpmadugsum.m
    cpmadugsum.e
    cpmadugsum.x
    cpmadugsum.t
    cpmadugsum.a
    cpmadugsum.b
    pmatcollpw3fi1
    syld3an3
    reximddv2
end
