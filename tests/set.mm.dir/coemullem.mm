include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "cdgr.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "plymulcl.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "nn0addcl.mm"
include "syl2an.mm"
include "fzfid.mm"
include "wf.mm"
include "coef3.mm"
include "adantr.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "fznn0sub.mm"
include "ffvelrnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "c1.mm"
include "cuz.mm"
include "cima.mm"
include "csn.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "sumeq12dv.mm"
include "sumex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "w3a.mm"
include "simp2r.mm"
include "simp2l.mm"
include "nn0red.mm"
include "simp3l.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "lesubadd2d.mm"
include "simp3r.mm"
include "leadd1dd.mm"
include "cr.mm"
include "readdcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "mtod.mm"
include "simpr.mm"
include "dgrub.mm"
include "3expia.mm"
include "syl2anc.mm"
include "necon1bd.mm"
include "mpd.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "impl.mm"
include "simpl.mm"
include "imp.mm"
include "oveq1d.mm"
include "ad3antrrr.mm"
include "ad2antlr.mm"
include "mul02d.mm"
include "pm2.61dan.mm"
include "sumeq2dv.mm"
include "wss.mm"
include "cfn.mm"
include "wo.mm"
include "fzfi.mm"
include "olci.mm"
include "sumz.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "expr.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "wb.mm"
include "plyco0.mm"
include "mpbird.mm"
include "cexp.mm"
include "dgrub2.mm"
include "coeid.mm"
include "plymullem1.mm"
include "sumeq2i.mm"
include "mpteq2i.mm"
include "syl6eqr.mm"
include "coeeq.mm"
include "dgrle.mm"
include "jca.mm"

theorem coemullem
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume coefv0.1: |- A = ( coeff ` F )
  assume coeadd.2: |- B = ( coeff ` G )
  assume coeadd.3: |- M = ( deg ` F )
  assume coeadd.4: |- N = ( deg ` G )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint B k
  disjoint B n
  disjoint F k
  disjoint F n
  disjoint M k
  disjoint G k
  disjoint G n
  disjoint N k
  disjoint N n
  disjoint S k
  disjoint S n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B j
  disjoint B y
  disjoint B z
  disjoint F j
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint M j
  disjoint M z
  disjoint G j
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint N j
  disjoint N z
  disjoint S j
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( ( coeff ` ( F oF x. G ) ) = ( n e. NN0 |-> sum_ k e. ( 0 ... n ) ( ( A ` k ) x. ( B ` ( n - k ) ) ) ) /\ ( deg ` ( F oF x. G ) ) <_ ( M + N ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    cmul
    cof
    co
    #
    ccoe
    cfv
    vn
    cn0
    cc0
    vn
    cv
    #
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    @5
    @7
    cmin
    co
    #
    cB
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wceq
    @4
    cdgr
    cfv
    cM
    cN
    caddc
    co
    #
    cle
    wbr
    @3
    vz
    @13
    cc
    vj
    @4
    @14
    cS
    cF
    cG
    plymulcl
    #
    @1
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @14
    cn0
    wcel
    #
    @2
    @1
    cM
    cF
    cdgr
    cfv
    cn0
    coeadd.3
    cS
    cF
    dgrcl
    syl5eqel
    #
    @2
    cN
    cG
    cdgr
    cfv
    cn0
    coeadd.4
    cS
    cG
    dgrcl
    syl5eqel
    #
    cM
    cN
    nn0addcl
    syl2an
    #
    @3
    vn
    cn0
    @12
    cc
    @13
    @3
    @5
    cn0
    wcel
    #
    wa
    #
    @6
    @11
    vk
    @23
    cc0
    @5
    fzfid
    @23
    @7
    @6
    wcel
    #
    wa
    #
    @8
    @10
    @23
    cn0
    cc
    cA
    wf
    #
    @7
    cn0
    wcel
    #
    @8
    cc
    wcel
    @24
    @3
    @26
    @22
    @1
    @26
    @2
    cA
    cS
    cF
    coefv0.1
    coef3
    adantr
    #
    adantr
    @7
    @5
    elfznn0
    cn0
    cc
    @7
    cA
    ffvelrn
    syl2an
    @25
    cn0
    cc
    @9
    cB
    @3
    cn0
    cc
    cB
    wf
    #
    @22
    @24
    @2
    @29
    @1
    cB
    cS
    cG
    coeadd.2
    coef3
    adantl
    #
    ad2antrr
    @24
    @9
    cn0
    wcel
    @23
    @7
    cc0
    @5
    fznn0sub
    adantl
    ffvelrnd
    mulcld
    fsumcl
    @13
    eqid
    #
    fmptd
    #
    @3
    @13
    @14
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    #
    wceq
    #
    vj
    cv
    #
    @13
    cfv
    #
    cc0
    wne
    @35
    @14
    cle
    wbr
    #
    wi
    #
    vj
    cn0
    wral
    #
    @3
    @38
    vj
    cn0
    @3
    @35
    cn0
    wcel
    #
    wa
    @37
    @36
    cc0
    @3
    @40
    @37
    wn
    #
    @36
    cc0
    wceq
    @3
    @40
    @41
    wa
    #
    wa
    #
    @36
    cc0
    @35
    cfz
    co
    #
    @8
    @35
    @7
    cmin
    co
    #
    cB
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    @40
    @36
    @48
    wceq
    #
    @3
    @41
    vn
    @35
    @12
    @48
    cn0
    @13
    @5
    @35
    wceq
    #
    @6
    @44
    @11
    @47
    vk
    @5
    @35
    cc0
    cfz
    oveq2
    @50
    @11
    @47
    wceq
    @24
    @50
    @10
    @46
    @8
    cmul
    @50
    @9
    @45
    cB
    @5
    @35
    @7
    cmin
    oveq1
    fveq2d
    oveq2d
    adantr
    sumeq12dv
    @31
    @44
    @47
    vk
    sumex
    fvmpt
    #
    ad2antrl
    @43
    @48
    @44
    cc0
    vk
    csu
    #
    cc0
    @43
    @44
    @47
    cc0
    vk
    @43
    @7
    @44
    wcel
    #
    wa
    #
    @7
    cM
    cle
    wbr
    #
    @47
    cc0
    wceq
    #
    @43
    @53
    @55
    @56
    @3
    @42
    @53
    @55
    wa
    #
    @56
    @3
    @42
    @57
    w3a
    #
    @47
    @8
    cc0
    cmul
    co
    cc0
    @58
    @46
    cc0
    @8
    cmul
    @58
    @45
    cN
    cle
    wbr
    #
    wn
    @46
    cc0
    wceq
    @58
    @59
    @37
    @3
    @40
    @41
    @57
    simp2r
    @58
    @59
    @35
    @7
    cN
    caddc
    co
    #
    cle
    wbr
    #
    @37
    @58
    @35
    @7
    cN
    @58
    @35
    @3
    @40
    @41
    @57
    simp2l
    nn0red
    #
    @58
    @7
    @58
    @53
    @27
    @3
    @42
    @53
    @55
    simp3l
    #
    @7
    @35
    elfznn0
    #
    syl
    #
    nn0red
    #
    @58
    cN
    @3
    @42
    @17
    @57
    @2
    @17
    @1
    @20
    adantl
    #
    3ad2ant1
    nn0red
    #
    lesubadd2d
    @58
    @61
    @60
    @14
    cle
    wbr
    #
    @37
    @58
    @7
    cM
    cN
    @66
    @58
    cM
    @3
    @42
    @16
    @57
    @1
    @16
    @2
    @19
    adantr
    #
    3ad2ant1
    nn0red
    #
    @68
    @3
    @42
    @53
    @55
    simp3r
    leadd1dd
    @58
    @35
    cr
    wcel
    @60
    cr
    wcel
    @14
    cr
    wcel
    @61
    @69
    wa
    @37
    wi
    @62
    @58
    @7
    cN
    @66
    @68
    readdcld
    @58
    cM
    cN
    @71
    @68
    readdcld
    @35
    @60
    @14
    letr
    syl3anc
    mpan2d
    sylbid
    mtod
    @58
    @59
    @46
    cc0
    @58
    @2
    @45
    cn0
    wcel
    #
    @46
    cc0
    wne
    #
    @59
    wi
    @3
    @42
    @2
    @57
    @1
    @2
    simpr
    #
    3ad2ant1
    @58
    @53
    @72
    @63
    @7
    cc0
    @35
    fznn0sub
    #
    syl
    @2
    @72
    @73
    @59
    cB
    cS
    cG
    @45
    cN
    coeadd.2
    coeadd.4
    dgrub
    3expia
    syl2anc
    necon1bd
    mpd
    oveq2d
    @58
    @8
    @58
    cn0
    cc
    @7
    cA
    @3
    @42
    @26
    @57
    @28
    3ad2ant1
    @65
    ffvelrnd
    mul01d
    eqtrd
    3expia
    impl
    @54
    @55
    wn
    #
    wa
    #
    @47
    cc0
    @46
    cmul
    co
    cc0
    @77
    @8
    cc0
    @46
    cmul
    @54
    @76
    @8
    cc0
    wceq
    @54
    @55
    @8
    cc0
    @43
    @1
    @27
    @8
    cc0
    wne
    #
    @55
    wi
    @53
    @3
    @1
    @42
    @1
    @2
    simpl
    #
    adantr
    @64
    @1
    @27
    @78
    @55
    cA
    cS
    cF
    @7
    cM
    coefv0.1
    coeadd.3
    dgrub
    3expia
    syl2an
    necon1bd
    imp
    oveq1d
    @77
    @46
    @77
    cn0
    cc
    @45
    cB
    @3
    @29
    @42
    @53
    @76
    @30
    ad3antrrr
    @53
    @72
    @43
    @76
    @75
    ad2antlr
    ffvelrnd
    mul02d
    eqtrd
    pm2.61dan
    sumeq2dv
    @44
    cc0
    cuz
    cfv
    wss
    #
    @44
    cfn
    wcel
    #
    wo
    @52
    cc0
    wceq
    @81
    @80
    cc0
    @35
    fzfi
    olci
    @44
    vk
    cc0
    sumz
    ax-mp
    syl6eq
    eqtrd
    expr
    necon1ad
    ralrimiva
    @3
    @18
    cn0
    cc
    @13
    wf
    #
    @34
    @39
    wb
    @21
    @32
    @13
    vj
    @14
    plyco0
    syl2anc
    mpbird
    @3
    @4
    vz
    cc
    cc0
    @14
    cfz
    co
    #
    @48
    vz
    cv
    #
    @35
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    vz
    cc
    @83
    @36
    @85
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    @3
    vz
    cA
    cB
    cS
    vk
    vj
    cF
    cG
    cM
    cN
    @79
    @74
    @70
    @67
    @28
    @30
    @1
    cA
    cM
    c1
    caddc
    co
    cuz
    cfv
    cima
    @33
    wceq
    @2
    cA
    cS
    cF
    cM
    coefv0.1
    coeadd.3
    dgrub2
    adantr
    @2
    cB
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    @33
    wceq
    @1
    cB
    cS
    cG
    cN
    coeadd.2
    coeadd.4
    dgrub2
    adantl
    @1
    cF
    vz
    cc
    cc0
    cM
    cfz
    co
    @8
    @84
    @7
    cexp
    co
    #
    cmul
    co
    vk
    csu
    cmpt
    wceq
    @2
    vz
    cA
    cS
    vk
    cF
    cM
    coefv0.1
    coeadd.3
    coeid
    adantr
    @2
    cG
    vz
    cc
    cc0
    cN
    cfz
    co
    @7
    cB
    cfv
    @90
    cmul
    co
    vk
    csu
    cmpt
    wceq
    @1
    vz
    cB
    cS
    vk
    cG
    cN
    coeadd.2
    coeadd.4
    coeid
    adantl
    plymullem1
    vz
    cc
    @89
    @87
    @83
    @88
    @86
    vj
    @35
    @83
    wcel
    #
    @36
    @48
    @85
    cmul
    @91
    @40
    @49
    @35
    @14
    elfznn0
    #
    @51
    syl
    oveq1d
    sumeq2i
    mpteq2i
    syl6eqr
    #
    coeeq
    @3
    vz
    @36
    cc
    vj
    @4
    @14
    @15
    @21
    @3
    @82
    @40
    @36
    cc
    wcel
    @91
    @32
    @92
    cn0
    cc
    @35
    @13
    ffvelrn
    syl2an
    @93
    dgrle
    jca
end
