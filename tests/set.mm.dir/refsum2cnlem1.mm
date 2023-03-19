include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "caddc.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wnfc.mm"
include "wceq.mm"
include "cif.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "a1i.mm"
include "1cnd.mm"
include "2cnd.mm"
include "1ex.mm"
include "prid1.mm"
include "ifcld.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "fvmptg.mm"
include "sylancr.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "adantr.mm"
include "fveq1d.mm"
include "cr.mm"
include "wf.mm"
include "cuni.mm"
include "cnf.mm"
include "syl.mm"
include "ctopon.mm"
include "toponuni.mm"
include "eqcomd.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "unieqi.mm"
include "uniretop.mm"
include "eqtr4i.mm"
include "feq23d.mm"
include "mpbid.mm"
include "anim1i.mm"
include "ffvelrn.mm"
include "recn.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "2ex.mm"
include "prid2.mm"
include "1ne2.mm"
include "nesymi.mm"
include "iffalsei.mm"
include "wne.mm"
include "fveq2.mm"
include "adantl.mm"
include "sumpair.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "mpteq2da.mm"
include "cfn.mm"
include "prfi.mm"
include "wal.mm"
include "wral.mm"
include "ax-gen.mm"
include "nfeq.mm"
include "fveq1.mm"
include "a1d.mm"
include "ralrimi.mm"
include "mpteq12f.mm"
include "wfn.mm"
include "retopon.mm"
include "eqeltri.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffn.mm"
include "dffn5f.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "wo.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "orcd.mm"
include "wn.mm"
include "neeq2.mm"
include "mpbiri.mm"
include "necomd.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "olcd.mm"
include "elpri.mm"
include "mpjaodan.mm"
include "refsumcn.mm"
include "eqeltrrd.mm"

theorem refsum2cnlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  assume refsum2cnlem1.1: |- F/_ x A
  assume refsum2cnlem1.2: |- F/_ x F
  assume refsum2cnlem1.3: |- F/_ x G
  assume refsum2cnlem1.4: |- F/ x ph
  assume refsum2cnlem1.5: |- A = ( k e. { 1 , 2 } |-> if ( k = 1 , F , G ) )
  assume refsum2cnlem1.6: |- K = ( topGen ` ran (,) )
  assume refsum2cnlem1.7: |- ( ph -> J e. ( TopOn ` X ) )
  assume refsum2cnlem1.8: |- ( ph -> F e. ( J Cn K ) )
  assume refsum2cnlem1.9: |- ( ph -> G e. ( J Cn K ) )

  disjoint k x
  disjoint J k
  disjoint J x
  disjoint F k
  disjoint G k
  disjoint K k
  disjoint K x
  disjoint X k
  disjoint X x
  disjoint k ph
  assert |- ( ph -> ( x e. X |-> ( ( F ` x ) + ( G ` x ) ) ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    c1
    c2
    cpr
    #
    vx
    cv
    #
    vk
    cv
    #
    cA
    cfv
    #
    cfv
    #
    vk
    csu
    #
    cmpt
    vx
    cX
    @1
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    caddc
    co
    #
    cmpt
    cJ
    cK
    ccn
    co
    #
    wph
    vx
    cX
    @5
    @8
    refsum2cnlem1.4
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @5
    @1
    c1
    cA
    cfv
    #
    cfv
    #
    @1
    c2
    cA
    cfv
    #
    cfv
    #
    caddc
    co
    @8
    @11
    c1
    c2
    @4
    @13
    vk
    @15
    cc
    cc
    vk
    @13
    wnfc
    @11
    vk
    @1
    @12
    vk
    c1
    cA
    vk
    cA
    vk
    @0
    @2
    c1
    wceq
    #
    cF
    cG
    cif
    #
    cmpt
    refsum2cnlem1.5
    vk
    @0
    @17
    nfmpt1
    nfcxfr
    #
    vk
    c1
    nfcv
    nffv
    vk
    @1
    nfcv
    #
    nffv
    a1i
    vk
    @15
    wnfc
    @11
    vk
    @1
    @14
    vk
    c2
    cA
    @18
    vk
    c2
    nfcv
    nffv
    @19
    nffv
    a1i
    @11
    1cnd
    @11
    2cnd
    @11
    @13
    @6
    cc
    @11
    @1
    @12
    cF
    wph
    @12
    cF
    wceq
    @10
    wph
    @12
    c1
    c1
    wceq
    #
    cF
    cG
    cif
    #
    cF
    wph
    c1
    @0
    wcel
    @21
    @9
    wcel
    @12
    @21
    wceq
    c1
    c2
    1ex
    prid1
    wph
    @20
    cF
    cG
    @9
    refsum2cnlem1.8
    refsum2cnlem1.9
    ifcld
    vk
    c1
    @17
    @21
    @0
    @9
    cA
    @16
    @16
    @20
    cF
    cG
    @2
    c1
    c1
    eqeq1
    ifbid
    refsum2cnlem1.5
    fvmptg
    sylancr
    @20
    cF
    cG
    c1
    eqid
    iftruei
    syl6eq
    adantr
    fveq1d
    #
    @11
    cX
    cr
    cF
    wf
    #
    @10
    wa
    @6
    cr
    wcel
    @6
    cc
    wcel
    wph
    @23
    @10
    wph
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
    #
    @23
    wph
    cF
    @9
    wcel
    #
    @26
    refsum2cnlem1.8
    cF
    cJ
    cK
    @24
    @25
    @24
    eqid
    #
    @25
    eqid
    #
    cnf
    syl
    wph
    @24
    @25
    cX
    cr
    cF
    wph
    cX
    @24
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cX
    @24
    wceq
    refsum2cnlem1.7
    cX
    cJ
    toponuni
    syl
    eqcomd
    #
    @25
    cr
    wceq
    wph
    @25
    cioo
    crn
    ctg
    cfv
    #
    cuni
    cr
    cK
    @32
    refsum2cnlem1.6
    unieqi
    uniretop
    eqtr4i
    a1i
    #
    feq23d
    mpbid
    anim1i
    cX
    cr
    @1
    cF
    ffvelrn
    @6
    recn
    3syl
    eqeltrd
    @11
    @15
    @7
    cc
    @11
    @1
    @14
    cG
    wph
    @14
    cG
    wceq
    @10
    wph
    @14
    c2
    c1
    wceq
    #
    cF
    cG
    cif
    #
    cG
    wph
    c2
    @0
    wcel
    @35
    @9
    wcel
    @14
    @35
    wceq
    c1
    c2
    2ex
    prid2
    wph
    @34
    cF
    cG
    @9
    refsum2cnlem1.8
    refsum2cnlem1.9
    ifcld
    vk
    c2
    @17
    @35
    @0
    @9
    cA
    @2
    c2
    wceq
    #
    @16
    @34
    cF
    cG
    @2
    c2
    c1
    eqeq1
    ifbid
    refsum2cnlem1.5
    fvmptg
    sylancr
    @34
    cF
    cG
    c1
    c2
    1ne2
    nesymi
    iffalsei
    syl6eq
    adantr
    fveq1d
    #
    @11
    cX
    cr
    cG
    wf
    #
    @10
    wa
    @7
    cr
    wcel
    @7
    cc
    wcel
    wph
    @38
    @10
    wph
    @24
    @25
    cG
    wf
    #
    @38
    wph
    cG
    @9
    wcel
    #
    @39
    refsum2cnlem1.9
    cG
    cJ
    cK
    @24
    @25
    @28
    @29
    cnf
    syl
    wph
    @24
    @25
    cX
    cr
    cG
    @31
    @33
    feq23d
    mpbid
    anim1i
    cX
    cr
    @1
    cG
    ffvelrn
    @7
    recn
    3syl
    eqeltrd
    c1
    c2
    wne
    #
    @11
    1ne2
    a1i
    @16
    @4
    @13
    wceq
    @11
    @16
    @1
    @3
    @12
    @2
    c1
    cA
    fveq2
    fveq1d
    adantl
    @36
    @4
    @15
    wceq
    @11
    @36
    @1
    @3
    @14
    @2
    c2
    cA
    fveq2
    fveq1d
    adantl
    sumpair
    @11
    @13
    @6
    @15
    @7
    caddc
    @22
    @37
    oveq12d
    eqtrd
    mpteq2da
    wph
    vx
    @0
    @4
    vk
    cJ
    cK
    cX
    refsum2cnlem1.4
    refsum2cnlem1.6
    refsum2cnlem1.7
    @0
    cfn
    wcel
    wph
    c1
    c2
    prfi
    a1i
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @3
    cF
    wceq
    #
    vx
    cX
    @4
    cmpt
    #
    @9
    wcel
    #
    @3
    cG
    wceq
    #
    wph
    @44
    @46
    @42
    wph
    @44
    wa
    #
    @45
    cF
    @9
    @48
    @45
    vx
    cX
    @6
    cmpt
    #
    cF
    @44
    @45
    @49
    wceq
    #
    wph
    @44
    cX
    cX
    wceq
    #
    vx
    wal
    #
    @4
    @6
    wceq
    #
    vx
    cX
    wral
    @50
    @51
    vx
    cX
    eqid
    ax-gen
    #
    @44
    @53
    vx
    cX
    vx
    @3
    cF
    vx
    @2
    cA
    refsum2cnlem1.1
    vx
    @2
    nfcv
    nffv
    #
    refsum2cnlem1.2
    nfeq
    @44
    @53
    @10
    @1
    @3
    cF
    fveq1
    a1d
    ralrimi
    vx
    cX
    @4
    cX
    @6
    mpteq12f
    sylancr
    adantl
    wph
    cF
    @49
    wceq
    #
    @44
    wph
    cF
    cX
    wfn
    #
    @56
    wph
    @23
    @57
    wph
    @30
    cK
    cr
    ctopon
    cfv
    #
    wcel
    #
    @27
    @23
    refsum2cnlem1.7
    @59
    wph
    cK
    @32
    @58
    refsum2cnlem1.6
    retopon
    eqeltri
    a1i
    #
    refsum2cnlem1.8
    cF
    cJ
    cK
    cX
    cr
    cnf2
    syl3anc
    cX
    cr
    cF
    ffn
    syl
    vx
    cX
    cF
    refsum2cnlem1.2
    dffn5f
    sylib
    adantr
    eqtr4d
    wph
    @27
    @44
    refsum2cnlem1.8
    adantr
    eqeltrd
    adantlr
    wph
    @47
    @46
    @42
    wph
    @47
    wa
    #
    @45
    cG
    @9
    @61
    @45
    vx
    cX
    @7
    cmpt
    #
    cG
    @47
    @45
    @62
    wceq
    #
    wph
    @47
    @52
    @4
    @7
    wceq
    #
    vx
    cX
    wral
    @63
    @54
    @47
    @64
    vx
    cX
    vx
    @3
    cG
    @55
    refsum2cnlem1.3
    nfeq
    @47
    @64
    @10
    @1
    @3
    cG
    fveq1
    a1d
    ralrimi
    vx
    cX
    @4
    cX
    @7
    mpteq12f
    sylancr
    adantl
    wph
    cG
    @62
    wceq
    #
    @47
    wph
    cG
    cX
    wfn
    #
    @65
    wph
    @38
    @66
    wph
    @30
    @59
    @40
    @38
    refsum2cnlem1.7
    @60
    refsum2cnlem1.9
    cG
    cJ
    cK
    cX
    cr
    cnf2
    syl3anc
    cX
    cr
    cG
    ffn
    syl
    vx
    cX
    cG
    refsum2cnlem1.3
    dffn5f
    sylib
    adantr
    eqtr4d
    wph
    @40
    @47
    refsum2cnlem1.9
    adantr
    eqeltrd
    adantlr
    @43
    @16
    @44
    @47
    wo
    @36
    @43
    @16
    wa
    @44
    @47
    @43
    @16
    @3
    @17
    cF
    @43
    @42
    @17
    @9
    wcel
    #
    @3
    @17
    wceq
    #
    wph
    @42
    simpr
    wph
    @67
    @42
    wph
    @16
    cF
    cG
    @9
    refsum2cnlem1.8
    refsum2cnlem1.9
    ifcld
    adantr
    vk
    @0
    @17
    @9
    cA
    refsum2cnlem1.5
    fvmpt2
    syl2anc
    #
    @16
    cF
    cG
    iftrue
    sylan9eq
    orcd
    @43
    @36
    wa
    #
    @47
    @44
    @70
    @3
    @17
    cG
    @43
    @68
    @36
    @69
    adantr
    @70
    @16
    cF
    cG
    @36
    @16
    wn
    @43
    @36
    @2
    c1
    @36
    c1
    @2
    @36
    c1
    @2
    wne
    @41
    1ne2
    @2
    c2
    c1
    neeq2
    mpbiri
    necomd
    neneqd
    adantl
    iffalsed
    eqtrd
    olcd
    @42
    @16
    @36
    wo
    wph
    @2
    c1
    c2
    elpri
    adantl
    mpjaodan
    mpjaodan
    refsumcn
    eqeltrrd
end
