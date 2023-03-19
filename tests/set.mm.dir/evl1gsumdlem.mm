include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "ralunb.mm"
include "csb.mm"
include "cplusg.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "oveq2i.mm"
include "cvv.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3ad2ant3.mm"
include "ad2antrr.mm"
include "simpll1.mm"
include "rspcsbela.mm"
include "expcom.mm"
include "adantl.mm"
include "adantr.mm"
include "imp.mm"
include "vex.mm"
include "a1i.mm"
include "simpll2.mm"
include "vsnid.mm"
include "mpan.mm"
include "csbeq1.mm"
include "gsumunsn.mm"
include "syl5eq.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "simplr.mm"
include "gsummptcl.mm"
include "eqidd.mm"
include "jca.mm"
include "evl1addd.mm"
include "simprd.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "csbfv12.mm"
include "csbfv2g.mm"
include "ax-mp.mm"
include "csbconstg.mm"
include "fveq12i.mm"
include "eqtri.mm"
include "fveval1fvcl.mm"
include "syl5eqel.mm"
include "nffv.mm"
include "csbhypf.mm"
include "syl6req.mm"
include "exp31.mm"
include "com23.mm"
include "ex.mm"
include "a2d.mm"
include "imp4b.mm"
include "syl5bi.mm"

theorem evl1gsumdlem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cU: class U
  let vm: setvar m
  let cM: class M
  let cO: class O
  let cY: class Y
  let va: setvar a
  let vy: setvar y
  assume evl1gsumd.q: |- O = ( eval1 ` R )
  assume evl1gsumd.p: |- P = ( Poly1 ` R )
  assume evl1gsumd.b: |- B = ( Base ` R )
  assume evl1gsumd.u: |- U = ( Base ` P )
  assume evl1gsumd.r: |- ( ph -> R e. CRing )
  assume evl1gsumd.y: |- ( ph -> Y e. B )

  disjoint a x
  disjoint m x
  disjoint O x
  disjoint U x
  disjoint Y x
  disjoint B y
  disjoint M y
  disjoint O y
  disjoint P y
  disjoint U y
  disjoint Y y
  disjoint a y
  disjoint x y
  disjoint m y
  disjoint R y
  disjoint ph y
  assert |- ( ( m e. Fin /\ -. a e. m /\ ph ) -> ( ( A. x e. m M e. U -> ( ( O ` ( P gsum ( x e. m |-> M ) ) ) ` Y ) = ( R gsum ( x e. m |-> ( ( O ` M ) ` Y ) ) ) ) -> ( A. x e. ( m u. { a } ) M e. U -> ( ( O ` ( P gsum ( x e. ( m u. { a } ) |-> M ) ) ) ` Y ) = ( R gsum ( x e. ( m u. { a } ) |-> ( ( O ` M ) ` Y ) ) ) ) ) )

  proof
    vm
    cv
    #
    cfn
    wcel
    #
    va
    cv
    #
    @0
    wcel
    wn
    #
    wph
    w3a
    #
    cM
    cU
    wcel
    #
    vx
    @0
    wral
    #
    cY
    cP
    vx
    @0
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
    cfv
    cfv
    #
    cR
    vx
    @0
    cY
    cM
    cO
    cfv
    #
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    #
    @5
    vx
    @0
    @2
    csn
    #
    cun
    #
    wral
    #
    cY
    cP
    vx
    @17
    cM
    cmpt
    #
    cgsu
    co
    #
    cO
    cfv
    #
    cfv
    #
    cR
    vx
    @17
    @11
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @18
    @6
    @5
    vx
    @16
    wral
    #
    wa
    @4
    @15
    wa
    @25
    @5
    vx
    @0
    @16
    ralunb
    @4
    @15
    @6
    @26
    @25
    @4
    @6
    @14
    @26
    @25
    wi
    #
    @4
    @6
    @14
    @27
    wi
    @4
    @6
    wa
    #
    @26
    @14
    @25
    @28
    @26
    @14
    @25
    @28
    @26
    wa
    #
    @14
    wa
    @22
    @13
    cY
    vx
    @2
    cM
    csb
    #
    cO
    cfv
    #
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @24
    @29
    @14
    @22
    @9
    @32
    @33
    co
    #
    @34
    @29
    @22
    cY
    @8
    @30
    cP
    cplusg
    cfv
    #
    co
    #
    cO
    cfv
    #
    cfv
    #
    @35
    @29
    cY
    @21
    @38
    @29
    @20
    @37
    cO
    @29
    @20
    cP
    vy
    @0
    vx
    vy
    cv
    #
    cM
    csb
    #
    cmpt
    #
    cgsu
    co
    #
    @30
    @36
    co
    #
    @37
    @29
    @20
    cP
    vy
    @17
    @41
    cmpt
    #
    cgsu
    co
    @44
    @19
    @45
    cP
    cgsu
    vx
    vy
    @17
    cM
    @41
    vy
    cM
    nfcv
    #
    vx
    @40
    cM
    nfcsb1v
    #
    vx
    @40
    cM
    csbeq1a
    #
    cbvmpt
    oveq2i
    @29
    @0
    cU
    @36
    vy
    cP
    @2
    cvv
    @41
    @30
    evl1gsumd.u
    @36
    eqid
    #
    @4
    cP
    ccmn
    wcel
    #
    @6
    @26
    wph
    @1
    @50
    @3
    wph
    cP
    crg
    wcel
    #
    @50
    wph
    cR
    crg
    wcel
    #
    @51
    wph
    cR
    ccrg
    wcel
    #
    @52
    evl1gsumd.r
    cR
    crngring
    syl
    #
    cP
    cR
    evl1gsumd.p
    ply1ring
    syl
    cP
    ringcmn
    syl
    3ad2ant3
    ad2antrr
    #
    @1
    @3
    wph
    @6
    @26
    simpll1
    #
    @29
    @40
    @0
    wcel
    #
    @41
    cU
    wcel
    #
    @28
    @57
    @58
    wi
    #
    @26
    @6
    @59
    @4
    @57
    @6
    @58
    vx
    @40
    @0
    cM
    cU
    rspcsbela
    expcom
    adantl
    adantr
    imp
    #
    @2
    cvv
    wcel
    @29
    va
    vex
    a1i
    #
    @1
    @3
    wph
    @6
    @26
    simpll2
    #
    @26
    @30
    cU
    wcel
    #
    @28
    @2
    @16
    wcel
    @26
    @63
    va
    vsnid
    vx
    @2
    @16
    cM
    cU
    rspcsbela
    mpan
    adantl
    #
    vx
    @40
    @2
    cM
    csbeq1
    gsumunsn
    syl5eq
    @43
    @8
    @30
    @36
    @42
    @7
    cP
    cgsu
    @7
    @42
    vx
    vy
    @0
    cM
    @41
    @46
    @47
    @48
    cbvmpt
    eqcomi
    oveq2i
    oveq1i
    syl6eq
    fveq2d
    fveq1d
    @29
    @37
    cU
    wcel
    @39
    @35
    wceq
    @29
    cB
    cP
    @33
    @36
    cR
    cU
    @8
    @30
    cO
    @9
    @32
    cY
    evl1gsumd.q
    evl1gsumd.p
    evl1gsumd.b
    evl1gsumd.u
    @4
    @53
    @6
    @26
    wph
    @1
    @53
    @3
    evl1gsumd.r
    3ad2ant3
    ad2antrr
    #
    @4
    cY
    cB
    wcel
    #
    @6
    @26
    wph
    @1
    @66
    @3
    evl1gsumd.y
    3ad2ant3
    ad2antrr
    #
    @29
    @8
    cU
    wcel
    @9
    @9
    wceq
    @29
    cU
    vx
    cP
    @0
    cM
    evl1gsumd.u
    @55
    @56
    @4
    @6
    @26
    simplr
    gsummptcl
    @29
    @9
    eqidd
    jca
    @29
    @63
    @32
    @32
    wceq
    @64
    @29
    @32
    eqidd
    jca
    @49
    @33
    eqid
    #
    evl1addd
    simprd
    eqtrd
    @9
    @13
    @32
    @33
    oveq1
    sylan9eq
    @29
    @34
    @24
    wceq
    @14
    @29
    @24
    cR
    vy
    @0
    vx
    @40
    @11
    csb
    #
    cmpt
    #
    cgsu
    co
    #
    @32
    @33
    co
    #
    @34
    @29
    @24
    cR
    vy
    @17
    @69
    cmpt
    #
    cgsu
    co
    @72
    @23
    @73
    cR
    cgsu
    vx
    vy
    @17
    @11
    @69
    vy
    @11
    nfcv
    #
    vx
    @40
    @11
    nfcsb1v
    #
    vx
    @40
    @11
    csbeq1a
    #
    cbvmpt
    oveq2i
    @29
    @0
    cB
    @33
    vy
    cR
    @2
    cvv
    @69
    @32
    evl1gsumd.b
    @68
    @4
    cR
    ccmn
    wcel
    #
    @6
    @26
    wph
    @1
    @77
    @3
    wph
    @52
    @77
    @54
    cR
    ringcmn
    syl
    3ad2ant3
    ad2antrr
    @56
    @29
    @57
    wa
    #
    @69
    cY
    @41
    cO
    cfv
    #
    cfv
    #
    cB
    @69
    vx
    @40
    cY
    csb
    #
    vx
    @40
    @10
    csb
    #
    cfv
    @80
    vx
    @40
    cY
    @10
    csbfv12
    @81
    cY
    @82
    @79
    @40
    cvv
    wcel
    #
    @82
    @79
    wceq
    vy
    vex
    #
    vx
    @40
    cM
    cvv
    cO
    csbfv2g
    ax-mp
    @83
    @81
    cY
    wceq
    @84
    vx
    @40
    cY
    cvv
    csbconstg
    ax-mp
    fveq12i
    eqtri
    @78
    cB
    cP
    cR
    cU
    @41
    cO
    cY
    evl1gsumd.q
    evl1gsumd.p
    evl1gsumd.b
    evl1gsumd.u
    @29
    @53
    @57
    @65
    adantr
    @29
    @66
    @57
    @67
    adantr
    @60
    fveval1fvcl
    syl5eqel
    @61
    @62
    @29
    cB
    cP
    cR
    cU
    @30
    cO
    cY
    evl1gsumd.q
    evl1gsumd.p
    evl1gsumd.b
    evl1gsumd.u
    @65
    @67
    @64
    fveval1fvcl
    vx
    vy
    @2
    @11
    @32
    vx
    @2
    nfcv
    vx
    cY
    @31
    vx
    @30
    cO
    vx
    cO
    nfcv
    vx
    @2
    cM
    nfcsb1v
    nffv
    vx
    cY
    nfcv
    nffv
    vx
    cv
    @2
    wceq
    #
    cY
    @10
    @31
    @85
    cM
    @30
    cO
    vx
    @2
    cM
    csbeq1a
    fveq2d
    fveq1d
    csbhypf
    gsumunsn
    syl5eq
    @71
    @13
    @32
    @33
    @70
    @12
    cR
    cgsu
    @12
    @70
    vx
    vy
    @0
    @11
    @69
    @74
    @75
    @76
    cbvmpt
    eqcomi
    oveq2i
    oveq1i
    syl6req
    adantr
    eqtrd
    exp31
    com23
    ex
    a2d
    imp4b
    syl5bi
    ex
end
