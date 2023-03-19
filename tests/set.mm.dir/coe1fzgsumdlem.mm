include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cco1.mm"
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
include "ply1ring.mm"
include "syl.mm"
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
include "cn0.mm"
include "simplr.mm"
include "gsummptcl.mm"
include "coe1addfv.mm"
include "syl31anc.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "cbs.mm"
include "csbfv12.mm"
include "csbfv2g.mm"
include "ax-mp.mm"
include "csbconstg.mm"
include "fveq12i.mm"
include "eqtri.mm"
include "wf.mm"
include "coe1f.mm"
include "ffvelrnd.mm"
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

theorem coe1fzgsumdlem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let vm: setvar m
  let cK: class K
  let cM: class M
  let va: setvar a
  let vy: setvar y
  assume coe1fzgsumd.p: |- P = ( Poly1 ` R )
  assume coe1fzgsumd.b: |- B = ( Base ` P )
  assume coe1fzgsumd.r: |- ( ph -> R e. Ring )
  assume coe1fzgsumd.k: |- ( ph -> K e. NN0 )

  disjoint B x
  disjoint K x
  disjoint m x
  disjoint a x
  disjoint B y
  disjoint x y
  disjoint K y
  disjoint M y
  disjoint P y
  disjoint R y
  disjoint ph y
  disjoint m y
  disjoint a y
  assert |- ( ( m e. Fin /\ -. a e. m /\ ph ) -> ( ( A. x e. m M e. B -> ( ( coe1 ` ( P gsum ( x e. m |-> M ) ) ) ` K ) = ( R gsum ( x e. m |-> ( ( coe1 ` M ) ` K ) ) ) ) -> ( A. x e. ( m u. { a } ) M e. B -> ( ( coe1 ` ( P gsum ( x e. ( m u. { a } ) |-> M ) ) ) ` K ) = ( R gsum ( x e. ( m u. { a } ) |-> ( ( coe1 ` M ) ` K ) ) ) ) ) )

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
    cB
    wcel
    #
    vx
    @0
    wral
    #
    cK
    cP
    vx
    @0
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    cfv
    #
    cR
    vx
    @0
    cK
    cM
    cco1
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
    cK
    cP
    vx
    @17
    cM
    cmpt
    #
    cgsu
    co
    #
    cco1
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
    cK
    vx
    @2
    cM
    csb
    #
    cco1
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
    cK
    @8
    @30
    cP
    cplusg
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @35
    @29
    cK
    @21
    @38
    @29
    @20
    @37
    cco1
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
    cB
    @36
    vy
    cP
    @2
    cvv
    @41
    @30
    coe1fzgsumd.b
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
    coe1fzgsumd.r
    cP
    cR
    coe1fzgsumd.p
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
    cB
    wcel
    #
    @28
    @55
    @56
    wi
    #
    @26
    @6
    @57
    @4
    @55
    @6
    @56
    vx
    @40
    @0
    cM
    cB
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
    cB
    wcel
    #
    @28
    @2
    @16
    wcel
    @26
    @61
    va
    vsnid
    vx
    @2
    @16
    cM
    cB
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
    @52
    @8
    cB
    wcel
    @61
    cK
    cn0
    wcel
    #
    @39
    @35
    wceq
    @4
    @52
    @6
    @26
    wph
    @1
    @52
    @3
    coe1fzgsumd.r
    3ad2ant3
    ad2antrr
    @29
    cB
    vx
    cP
    @0
    cM
    coe1fzgsumd.b
    @53
    @54
    @4
    @6
    @26
    simplr
    gsummptcl
    @62
    @4
    @63
    @6
    @26
    wph
    @1
    @63
    @3
    coe1fzgsumd.k
    3ad2ant3
    #
    ad2antrr
    #
    cB
    @33
    @36
    cR
    @8
    @30
    cK
    cP
    coe1fzgsumd.p
    coe1fzgsumd.b
    @49
    @33
    eqid
    #
    coe1addfv
    syl31anc
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
    @67
    cmpt
    #
    cgsu
    co
    @70
    @23
    @71
    cR
    cgsu
    vx
    vy
    @17
    @11
    @67
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
    cR
    cbs
    cfv
    #
    @33
    vy
    cR
    @2
    cvv
    @67
    @32
    @75
    eqid
    #
    @66
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
    coe1fzgsumd.r
    cR
    ringcmn
    syl
    3ad2ant3
    ad2antrr
    @54
    @29
    @55
    wa
    #
    @67
    cK
    @41
    cco1
    cfv
    #
    cfv
    #
    @75
    @67
    vx
    @40
    cK
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
    cK
    @10
    csbfv12
    @81
    cK
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
    cco1
    csbfv2g
    ax-mp
    @83
    @81
    cK
    wceq
    @84
    vx
    @40
    cK
    cvv
    csbconstg
    ax-mp
    fveq12i
    eqtri
    @78
    cn0
    @75
    cK
    @79
    @78
    @56
    cn0
    @75
    @79
    wf
    @58
    @79
    cB
    cP
    cR
    @41
    @75
    @79
    eqid
    coe1fzgsumd.b
    coe1fzgsumd.p
    @76
    coe1f
    syl
    @28
    @63
    @26
    @55
    @4
    @63
    @6
    @64
    adantr
    ad2antrr
    ffvelrnd
    syl5eqel
    @59
    @60
    @29
    cn0
    @75
    cK
    @31
    @29
    @61
    cn0
    @75
    @31
    wf
    @62
    @31
    cB
    cP
    cR
    @30
    @75
    @31
    eqid
    coe1fzgsumd.b
    coe1fzgsumd.p
    @76
    coe1f
    syl
    @65
    ffvelrnd
    vx
    vy
    @2
    @11
    @32
    vx
    @2
    nfcv
    vx
    cK
    @31
    vx
    @30
    cco1
    vx
    cco1
    nfcv
    vx
    @2
    cM
    nfcsb1v
    nffv
    vx
    cK
    nfcv
    nffv
    vx
    cv
    @2
    wceq
    #
    cK
    @10
    @31
    @85
    cM
    @30
    cco1
    vx
    @2
    cM
    csbeq1a
    fveq2d
    fveq1d
    csbhypf
    gsumunsn
    syl5eq
    @69
    @13
    @32
    @33
    @68
    @12
    cR
    cgsu
    @12
    @68
    vx
    vy
    @0
    @11
    @67
    @72
    @73
    @74
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
