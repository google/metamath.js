include "cotp.mm"
include "cmmul.mm"
include "co.mm"
include "cxp.mm"
include "cmap.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cvv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cbs.mm"
include "cmulr.mm"
include "csb.mm"
include "wceq.mm"
include "df-mamu.mm"
include "a1i.mm"
include "wa.mm"
include "fvex.mm"
include "eqidd.mm"
include "xpeq2.mm"
include "oveq2d.mm"
include "id.mm"
include "mpt2eq123dv.mm"
include "csbie.mm"
include "xpeq12.mm"
include "simpr.mm"
include "xpeq1d.mm"
include "adantr.mm"
include "mpteq12dv.mm"
include "syl5eq.mm"
include "csbie2.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "cfn.mm"
include "wcel.mm"
include "ot1stg.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "ot2ndg.mm"
include "xpeq12d.mm"
include "oveq12d.mm"
include "ot3rdg.mm"
include "syl.mm"
include "oveqd.mm"
include "elex.mm"
include "otex.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "ovmpt2d.mm"

theorem mamufval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vp: setvar p
  let vr: setvar r
  let cX: class X
  let cY: class Y
  let cI: class I
  let cK: class K
  assume mamufval.f: |- F = ( R maMul <. M , N , P >. )
  assume mamufval.b: |- B = ( Base ` R )
  assume mamufval.t: |- .x. = ( .r ` R )
  assume mamufval.r: |- ( ph -> R e. V )
  assume mamufval.m: |- ( ph -> M e. Fin )
  assume mamufval.n: |- ( ph -> N e. Fin )
  assume mamufval.p: |- ( ph -> P e. Fin )

  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint .x. x
  disjoint .x. y
  disjoint .x. i
  disjoint .x. k
  disjoint i m
  disjoint i n
  disjoint i o
  disjoint i p
  disjoint i r
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j p
  disjoint j r
  disjoint k m
  disjoint k n
  disjoint k o
  disjoint k p
  disjoint k r
  disjoint m n
  disjoint m o
  disjoint m p
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n o
  disjoint n p
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint o p
  disjoint o r
  disjoint o x
  disjoint o y
  disjoint p r
  disjoint p x
  disjoint p y
  disjoint r x
  disjoint r y
  disjoint M o
  disjoint M r
  disjoint N o
  disjoint N r
  disjoint P o
  disjoint P r
  disjoint R o
  disjoint R r
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint o ph
  disjoint ph r
  disjoint B o
  disjoint B r
  disjoint .x. o
  disjoint .x. r
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint K i
  disjoint K j
  disjoint K k
  assert |- ( ph -> F = ( x e. ( B ^m ( M X. N ) ) , y e. ( B ^m ( N X. P ) ) |-> ( i e. M , k e. P |-> ( R gsum ( j e. N |-> ( ( i x j ) .x. ( j y k ) ) ) ) ) ) )

  proof
    wph
    cF
    cR
    cM
    cN
    cP
    cotp
    #
    cmmul
    co
    vx
    vy
    cB
    cM
    cN
    cxp
    #
    cmap
    co
    #
    cB
    cN
    cP
    cxp
    #
    cmap
    co
    #
    vi
    vk
    cM
    cP
    cR
    vj
    cN
    vi
    cv
    vj
    cv
    #
    vx
    cv
    co
    #
    @5
    vk
    cv
    vy
    cv
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cmpt2
    #
    mamufval.f
    wph
    vr
    vo
    cR
    @0
    cvv
    cvv
    vm
    vo
    cv
    #
    c1st
    cfv
    #
    c1st
    cfv
    #
    vn
    @14
    c2nd
    cfv
    #
    vp
    @13
    c2nd
    cfv
    #
    vx
    vy
    vr
    cv
    #
    cbs
    cfv
    #
    vm
    cv
    #
    vn
    cv
    #
    cxp
    #
    cmap
    co
    #
    @19
    @21
    vp
    cv
    #
    cxp
    #
    cmap
    co
    #
    vi
    vk
    @20
    @24
    @18
    vj
    @21
    @6
    @7
    @18
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cmpt2
    #
    csb
    #
    csb
    csb
    #
    @12
    cmmul
    cvv
    cmmul
    vr
    vo
    cvv
    cvv
    @34
    cmpt2
    wceq
    wph
    vx
    vy
    vi
    vj
    vk
    vm
    vn
    vo
    vr
    vp
    df-mamu
    a1i
    wph
    @18
    cR
    wceq
    #
    @13
    @0
    wceq
    #
    wa
    #
    wa
    #
    @34
    vx
    vy
    @19
    @15
    @16
    cxp
    #
    cmap
    co
    #
    @19
    @16
    @17
    cxp
    #
    cmap
    co
    #
    vi
    vk
    @15
    @17
    @18
    vj
    @16
    @28
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cmpt2
    #
    @12
    vm
    vn
    @15
    @16
    @33
    @46
    @14
    c1st
    fvex
    @14
    c2nd
    fvex
    @20
    @15
    wceq
    #
    @21
    @16
    wceq
    #
    wa
    #
    @33
    vx
    vy
    @23
    @19
    @21
    @17
    cxp
    #
    cmap
    co
    #
    vi
    vk
    @20
    @17
    @30
    cmpt2
    #
    cmpt2
    #
    @46
    vp
    @17
    @32
    @53
    @13
    c2nd
    fvex
    @24
    @17
    wceq
    #
    vx
    vy
    @23
    @26
    @31
    @23
    @51
    @52
    @54
    @23
    eqidd
    @54
    @25
    @50
    @19
    cmap
    @24
    @17
    @21
    xpeq2
    oveq2d
    @54
    vi
    vk
    @20
    @24
    @30
    @20
    @17
    @30
    @54
    @20
    eqidd
    @54
    id
    @54
    @30
    eqidd
    mpt2eq123dv
    mpt2eq123dv
    csbie
    @49
    vx
    vy
    @23
    @51
    @52
    @40
    @42
    @45
    @49
    @22
    @39
    @19
    cmap
    @20
    @15
    @21
    @16
    xpeq12
    oveq2d
    @49
    @50
    @41
    @19
    cmap
    @49
    @21
    @16
    @17
    @47
    @48
    simpr
    #
    xpeq1d
    oveq2d
    @49
    vi
    vk
    @20
    @17
    @30
    @15
    @17
    @44
    @47
    @47
    @48
    @47
    id
    adantr
    @49
    @17
    eqidd
    @49
    @29
    @43
    @18
    cgsu
    @49
    vj
    @21
    @28
    @16
    @28
    @55
    @49
    @28
    eqidd
    mpteq12dv
    oveq2d
    mpt2eq123dv
    mpt2eq123dv
    syl5eq
    csbie2
    @38
    vx
    vy
    @40
    @42
    @45
    @2
    @4
    @11
    @38
    @19
    cB
    @39
    @1
    cmap
    @38
    @19
    cR
    cbs
    cfv
    cB
    @38
    @18
    cR
    cbs
    wph
    @35
    @36
    simprl
    #
    fveq2d
    mamufval.b
    syl6eqr
    #
    @38
    @15
    cM
    @16
    cN
    @38
    @15
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    cM
    @36
    @15
    @59
    wceq
    wph
    @35
    @36
    @14
    @58
    c1st
    @13
    @0
    c1st
    fveq2
    #
    fveq2d
    ad2antll
    wph
    @59
    cM
    wceq
    #
    @37
    wph
    cM
    cfn
    wcel
    #
    cN
    cfn
    wcel
    #
    cP
    cfn
    wcel
    #
    @61
    mamufval.m
    mamufval.n
    mamufval.p
    cM
    cN
    cP
    cfn
    cfn
    cfn
    ot1stg
    syl3anc
    adantr
    eqtrd
    #
    @38
    @16
    @58
    c2nd
    cfv
    #
    cN
    @36
    @16
    @66
    wceq
    wph
    @35
    @36
    @14
    @58
    c2nd
    @60
    fveq2d
    ad2antll
    wph
    @66
    cN
    wceq
    #
    @37
    wph
    @62
    @63
    @64
    @67
    mamufval.m
    mamufval.n
    mamufval.p
    cM
    cN
    cP
    cfn
    cfn
    cfn
    ot2ndg
    syl3anc
    adantr
    eqtrd
    #
    xpeq12d
    oveq12d
    @38
    @19
    cB
    @41
    @3
    cmap
    @57
    @38
    @16
    cN
    @17
    cP
    @68
    @38
    @17
    @0
    c2nd
    cfv
    #
    cP
    @36
    @17
    @69
    wceq
    wph
    @35
    @13
    @0
    c2nd
    fveq2
    ad2antll
    wph
    @69
    cP
    wceq
    #
    @37
    wph
    @64
    @70
    mamufval.p
    cM
    cN
    cP
    cfn
    ot3rdg
    syl
    adantr
    eqtrd
    #
    xpeq12d
    oveq12d
    @38
    vi
    vk
    @15
    @17
    @44
    cM
    cP
    @10
    @65
    @71
    @38
    @18
    cR
    @43
    @9
    cgsu
    @56
    @38
    vj
    @16
    @28
    cN
    @8
    @68
    @38
    @27
    c.x
    @6
    @7
    @38
    @27
    cR
    cmulr
    cfv
    c.x
    @38
    @18
    cR
    cmulr
    @56
    fveq2d
    mamufval.t
    syl6eqr
    oveqd
    mpteq12dv
    oveq12d
    mpt2eq123dv
    mpt2eq123dv
    syl5eq
    wph
    cR
    cV
    wcel
    cR
    cvv
    wcel
    mamufval.r
    cR
    cV
    elex
    syl
    @0
    cvv
    wcel
    wph
    cM
    cN
    cP
    otex
    a1i
    @12
    cvv
    wcel
    wph
    vx
    vy
    @2
    @4
    @11
    cB
    @1
    cmap
    ovex
    cB
    @3
    cmap
    ovex
    mpt2ex
    a1i
    ovmpt2d
    syl5eq
end
