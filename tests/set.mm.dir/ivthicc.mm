include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "simpll.mm"
include "cr.mm"
include "cle.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1d.mm"
include "ad2antrr.mm"
include "wss.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "iccssre.mm"
include "sselda.mm"
include "adantr.mm"
include "simpr.mm"
include "simp2d.mm"
include "simp3d.mm"
include "iccss.mm"
include "syl22anc.mm"
include "sstrd.mm"
include "cc.mm"
include "ccncf.mm"
include "syldan.mm"
include "sylan.mm"
include "biimpa.mm"
include "3simpc.mm"
include "syl.mm"
include "ivthle.mm"
include "wi.mm"
include "wfn.mm"
include "wf.mm"
include "cncff.mm"
include "ffn.mm"
include "3syl.mm"
include "fnfvelrn.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "csn.mm"
include "simplr.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "cxr.mm"
include "rexrd.mm"
include "iccid.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "ivthle2.mm"
include "w3o.mm"
include "lttri4d.mm"
include "mpjao3dan.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ivthicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cM: class M
  let cN: class N
  let vz: setvar z
  let vy: setvar y
  assume ivthicc.1: |- ( ph -> A e. RR )
  assume ivthicc.2: |- ( ph -> B e. RR )
  assume ivthicc.3: |- ( ph -> M e. ( A [,] B ) )
  assume ivthicc.4: |- ( ph -> N e. ( A [,] B ) )
  assume ivthicc.5: |- ( ph -> ( A [,] B ) C_ D )
  assume ivthicc.7: |- ( ph -> F e. ( D -cn-> CC ) )
  assume ivthicc.8: |- ( ( ph /\ x e. ( A [,] B ) ) -> ( F ` x ) e. RR )

  disjoint D x
  disjoint F x
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint A x
  disjoint B x
  disjoint x z
  disjoint D z
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( ( F ` M ) [,] ( F ` N ) ) C_ ran F )

  proof
    wph
    vy
    cM
    cF
    cfv
    #
    cN
    cF
    cfv
    #
    cicc
    co
    #
    cF
    crn
    #
    wph
    vy
    cv
    #
    @2
    wcel
    #
    @4
    @3
    wcel
    #
    wph
    @5
    wa
    #
    cM
    cN
    clt
    wbr
    #
    @6
    cM
    cN
    wceq
    #
    cN
    cM
    clt
    wbr
    #
    @7
    @8
    wa
    #
    wph
    vz
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    vz
    cM
    cN
    cicc
    co
    #
    wrex
    @6
    wph
    @5
    @8
    simpll
    #
    @11
    vx
    cM
    cN
    cD
    @4
    cF
    vz
    wph
    cM
    cr
    wcel
    #
    @5
    @8
    wph
    @17
    cA
    cM
    cle
    wbr
    #
    cM
    cB
    cle
    wbr
    #
    wph
    cM
    cA
    cB
    cicc
    co
    #
    wcel
    #
    @17
    @18
    @19
    w3a
    #
    ivthicc.3
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @21
    @22
    wb
    ivthicc.1
    ivthicc.2
    cA
    cB
    cM
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    ad2antrr
    wph
    cN
    cr
    wcel
    #
    @5
    @8
    wph
    @27
    cA
    cN
    cle
    wbr
    #
    cN
    cB
    cle
    wbr
    #
    wph
    cN
    @20
    wcel
    #
    @27
    @28
    @29
    w3a
    #
    ivthicc.4
    wph
    @23
    @24
    @30
    @31
    wb
    ivthicc.1
    ivthicc.2
    cA
    cB
    cN
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    ad2antrr
    @7
    @4
    cr
    wcel
    #
    @8
    wph
    @2
    cr
    @4
    wph
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @2
    cr
    wss
    wph
    @21
    vx
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    vx
    @20
    wral
    #
    @35
    ivthicc.3
    wph
    @39
    vx
    @20
    ivthicc.8
    ralrimiva
    #
    @39
    @35
    vx
    cM
    @20
    @37
    cM
    wceq
    @38
    @0
    cr
    @37
    cM
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    wph
    @30
    @40
    @36
    ivthicc.4
    @41
    @39
    @36
    vx
    cN
    @20
    @37
    cN
    wceq
    @38
    @1
    cr
    @37
    cN
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    @0
    @1
    iccssre
    syl2anc
    sselda
    #
    adantr
    @7
    @8
    simpr
    wph
    @15
    cD
    wss
    @5
    @8
    wph
    @15
    @20
    cD
    wph
    @23
    @24
    @18
    @29
    @15
    @20
    wss
    ivthicc.1
    ivthicc.2
    wph
    @17
    @18
    @19
    @25
    simp2d
    wph
    @27
    @28
    @29
    @32
    simp3d
    cA
    cB
    cM
    cN
    iccss
    syl22anc
    #
    ivthicc.5
    sstrd
    #
    ad2antrr
    wph
    cF
    cD
    cc
    ccncf
    co
    wcel
    #
    @5
    @8
    ivthicc.7
    ad2antrr
    @11
    wph
    @37
    @15
    wcel
    #
    @39
    @16
    wph
    @48
    @37
    @20
    wcel
    #
    @39
    wph
    @15
    @20
    @37
    @45
    sselda
    ivthicc.8
    syldan
    sylan
    @7
    @0
    @4
    cle
    wbr
    #
    @4
    @1
    cle
    wbr
    #
    wa
    #
    @8
    @7
    @34
    @50
    @51
    w3a
    #
    @52
    wph
    @5
    @53
    wph
    @35
    @36
    @5
    @53
    wb
    @42
    @43
    @0
    @1
    @4
    elicc2
    syl2anc
    biimpa
    @34
    @50
    @51
    3simpc
    syl
    #
    adantr
    ivthle
    wph
    @14
    @6
    vz
    @15
    wph
    @12
    @15
    wcel
    @12
    cD
    wcel
    #
    @14
    @6
    wi
    #
    wph
    @15
    cD
    @12
    @46
    sselda
    wph
    @55
    wa
    @13
    @3
    wcel
    #
    @14
    @6
    wph
    cF
    cD
    wfn
    #
    @55
    @57
    wph
    @47
    cD
    cc
    cF
    wf
    @58
    ivthicc.7
    cD
    cc
    cF
    cncff
    cD
    cc
    cF
    ffn
    3syl
    #
    cD
    @12
    cF
    fnfvelrn
    sylan
    @13
    @4
    @3
    eleq1
    syl5ibcom
    #
    syldan
    rexlimdva
    sylc
    @7
    @9
    wa
    #
    @4
    @0
    @3
    @61
    @4
    @0
    csn
    #
    wcel
    @4
    @0
    wceq
    @61
    @4
    @2
    @62
    wph
    @5
    @9
    simplr
    @61
    @0
    @0
    cicc
    co
    #
    @2
    @62
    @61
    @0
    @1
    @0
    cicc
    @61
    cM
    cN
    cF
    @7
    @9
    simpr
    fveq2d
    oveq2d
    @61
    @0
    cxr
    wcel
    #
    @63
    @62
    wceq
    wph
    @64
    @5
    @9
    wph
    @0
    @42
    rexrd
    ad2antrr
    @0
    iccid
    syl
    eqtr3d
    eleqtrd
    @4
    @0
    elsni
    syl
    wph
    @0
    @3
    wcel
    #
    @5
    @9
    wph
    @58
    cM
    cD
    wcel
    @65
    @59
    wph
    @20
    cD
    cM
    ivthicc.5
    ivthicc.3
    sseldd
    cD
    cM
    cF
    fnfvelrn
    syl2anc
    ad2antrr
    eqeltrd
    @7
    @10
    wa
    #
    wph
    @14
    vz
    cN
    cM
    cicc
    co
    #
    wrex
    @6
    wph
    @5
    @10
    simpll
    #
    @66
    vx
    cN
    cM
    cD
    @4
    cF
    vz
    wph
    @27
    @5
    @10
    @33
    ad2antrr
    wph
    @17
    @5
    @10
    @26
    ad2antrr
    @7
    @34
    @10
    @44
    adantr
    @7
    @10
    simpr
    wph
    @67
    cD
    wss
    @5
    @10
    wph
    @67
    @20
    cD
    wph
    @23
    @24
    @28
    @19
    @67
    @20
    wss
    ivthicc.1
    ivthicc.2
    wph
    @27
    @28
    @29
    @32
    simp2d
    wph
    @17
    @18
    @19
    @25
    simp3d
    cA
    cB
    cN
    cM
    iccss
    syl22anc
    #
    ivthicc.5
    sstrd
    #
    ad2antrr
    wph
    @47
    @5
    @10
    ivthicc.7
    ad2antrr
    @66
    wph
    @37
    @67
    wcel
    #
    @39
    @68
    wph
    @71
    @49
    @39
    wph
    @67
    @20
    @37
    @69
    sselda
    ivthicc.8
    syldan
    sylan
    @7
    @52
    @10
    @54
    adantr
    ivthle2
    wph
    @14
    @6
    vz
    @67
    wph
    @12
    @67
    wcel
    @55
    @56
    wph
    @67
    cD
    @12
    @70
    sselda
    @60
    syldan
    rexlimdva
    sylc
    wph
    @8
    @9
    @10
    w3o
    @5
    wph
    cM
    cN
    @26
    @33
    lttri4d
    adantr
    mpjao3dan
    ex
    ssrdv
end
