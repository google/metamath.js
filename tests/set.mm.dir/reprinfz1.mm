include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cin.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "cn.mm"
include "nnex.mm"
include "a1i.mm"
include "ssexd.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "biimpa.mm"
include "adantr.mm"
include "wfn.mm"
include "wral.mm"
include "elmapfn.mm"
include "ad2antlr.mm"
include "wn.mm"
include "wrex.mm"
include "simplr.mm"
include "wne.mm"
include "cr.mm"
include "nn0red.mm"
include "ad3antrrr.mm"
include "wss.mm"
include "simpllr.mm"
include "mpbid.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "nnred.mm"
include "cfn.mm"
include "fzofi.mm"
include "ad4antr.mm"
include "ffvelrnda.mm"
include "fsumrecl.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "simpr.mm"
include "cz.mm"
include "nn0zd.mm"
include "fznn.mm"
include "syl.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "notbid.mm"
include "ltnled.mm"
include "mpbird.mm"
include "csn.mm"
include "cc.mm"
include "recnd.mm"
include "fveq2.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "nn0ge0.mm"
include "snssi.mm"
include "fsumless.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "ltned.mm"
include "necomd.mm"
include "r19.29an.mm"
include "neneqd.mm"
include "adantlr.mm"
include "pm2.65da.mm"
include "dfral2.mm"
include "sylibr.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "jca.mm"
include "ffnfv.mm"
include "fin.mm"
include "inex2.mm"
include "elmap.mm"
include "anasss.mm"
include "rabss3d.mm"
include "reprval.mm"
include "inss1.mm"
include "sstrd.mm"
include "3sstr4d.mm"
include "reprss.mm"
include "eqssd.mm"

theorem reprinfz1
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume reprinfz1.n: |- ( ph -> N e. NN0 )
  assume reprinfz1.s: |- ( ph -> S e. NN0 )
  assume reprinfz1.a: |- ( ph -> A C_ NN )


  assert |- ( ph -> ( A ( repr ` S ) N ) = ( ( A i^i ( 1 ... N ) ) ( repr ` S ) N ) )

  proof
    wph
    cA
    cN
    cS
    crepr
    cfv
    #
    co
    #
    cA
    c1
    cN
    cfz
    co
    #
    cin
    #
    cN
    @0
    co
    #
    wph
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    #
    vc
    cv
    #
    cfv
    #
    va
    csu
    #
    cN
    wceq
    #
    vc
    cA
    @5
    cmap
    co
    #
    crab
    @10
    vc
    @3
    @5
    cmap
    co
    #
    crab
    @1
    @4
    wph
    @10
    vc
    @11
    @12
    wph
    @7
    @11
    wcel
    #
    @10
    @7
    @12
    wcel
    #
    wph
    @13
    wa
    #
    @10
    wa
    #
    @5
    @3
    @7
    wf
    #
    @14
    @16
    @5
    cA
    @7
    wf
    #
    @5
    @2
    @7
    wf
    #
    wa
    @17
    @16
    @18
    @19
    @15
    @18
    @10
    wph
    @13
    @18
    wph
    cA
    cvv
    wcel
    @5
    cvv
    wcel
    @13
    @18
    wb
    #
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprinfz1.a
    ssexd
    cc0
    cS
    cfzo
    ovex
    #
    cA
    @5
    @7
    cvv
    cvv
    elmapg
    sylancl
    #
    biimpa
    adantr
    @16
    @7
    @5
    wfn
    #
    @8
    @2
    wcel
    #
    va
    @5
    wral
    #
    wa
    @19
    @16
    @23
    @25
    @13
    @23
    wph
    @10
    @7
    cA
    @5
    elmapfn
    ad2antlr
    @16
    vb
    cv
    #
    @7
    cfv
    #
    @2
    wcel
    #
    vb
    @5
    wral
    #
    @25
    @16
    @28
    wn
    #
    vb
    @5
    wrex
    #
    wn
    @29
    @16
    @31
    @10
    @15
    @10
    @31
    simplr
    @15
    @31
    @10
    wn
    @10
    @15
    @31
    wa
    @9
    cN
    @15
    @30
    @9
    cN
    wne
    vb
    @5
    @15
    @26
    @5
    wcel
    #
    wa
    #
    @30
    wa
    #
    cN
    @9
    @34
    cN
    @9
    wph
    cN
    cr
    wcel
    @13
    @32
    @30
    wph
    cN
    reprinfz1.n
    nn0red
    ad3antrrr
    #
    @34
    cN
    @27
    @9
    @35
    @34
    @27
    @34
    cA
    cn
    @27
    wph
    cA
    cn
    wss
    #
    @13
    @32
    @30
    reprinfz1.a
    ad3antrrr
    @34
    @5
    cA
    @26
    @7
    @34
    @13
    @18
    wph
    @13
    @32
    @30
    simpllr
    wph
    @20
    @13
    @32
    @30
    @22
    ad3antrrr
    mpbid
    #
    @15
    @32
    @30
    simplr
    #
    ffvelrnd
    sseldd
    #
    nnred
    #
    @34
    @5
    @8
    va
    @5
    cfn
    wcel
    @34
    cc0
    cS
    fzofi
    a1i
    #
    @34
    @6
    @5
    wcel
    #
    wa
    #
    @8
    @43
    cA
    cn
    @8
    wph
    @36
    @13
    @32
    @30
    @42
    reprinfz1.a
    ad4antr
    @34
    @5
    cA
    @6
    @7
    @37
    ffvelrnda
    sseldd
    #
    nnred
    #
    fsumrecl
    @34
    cN
    @27
    clt
    wbr
    @27
    cN
    cle
    wbr
    #
    wn
    #
    @34
    @30
    @47
    @33
    @30
    simpr
    @34
    @28
    @46
    @34
    @28
    @27
    cn
    wcel
    #
    @46
    wa
    #
    @46
    @34
    cN
    cz
    wcel
    #
    @28
    @49
    wb
    wph
    @50
    @13
    @32
    @30
    wph
    cN
    reprinfz1.n
    nn0zd
    #
    ad3antrrr
    @27
    cN
    fznn
    syl
    @34
    @48
    @46
    @39
    biantrurd
    bitr4d
    notbid
    mpbid
    @34
    cN
    @27
    @35
    @40
    ltnled
    mpbird
    @34
    @26
    csn
    #
    @8
    va
    csu
    #
    @27
    @9
    cle
    @34
    @32
    @27
    cc
    wcel
    @53
    @27
    wceq
    @38
    @34
    @27
    @40
    recnd
    @8
    @27
    va
    @26
    @5
    @6
    @26
    @7
    fveq2
    #
    sumsn
    syl2anc
    @34
    @5
    @8
    @52
    va
    @41
    @45
    @43
    @8
    cn0
    wcel
    cc0
    @8
    cle
    wbr
    @43
    @8
    @44
    nnnn0d
    @8
    nn0ge0
    syl
    @32
    @52
    @5
    wss
    @15
    @30
    @26
    @5
    snssi
    ad2antlr
    fsumless
    eqbrtrrd
    ltletrd
    ltned
    necomd
    r19.29an
    neneqd
    adantlr
    pm2.65da
    @28
    vb
    @5
    dfral2
    sylibr
    @24
    @28
    va
    vb
    @5
    @6
    @26
    wceq
    @8
    @27
    @2
    @54
    eleq1d
    cbvralv
    sylibr
    jca
    va
    @5
    @2
    @7
    ffnfv
    sylibr
    jca
    @5
    cA
    @2
    @7
    fin
    sylibr
    @3
    @5
    @7
    @2
    cA
    c1
    cN
    cfz
    ovex
    inex2
    @21
    elmap
    sylibr
    anasss
    rabss3d
    wph
    cA
    cS
    cN
    va
    vc
    reprinfz1.a
    @51
    reprinfz1.s
    reprval
    wph
    @3
    cS
    cN
    va
    vc
    wph
    @3
    cA
    cn
    @3
    cA
    wss
    wph
    cA
    @2
    inss1
    a1i
    #
    reprinfz1.a
    sstrd
    @51
    reprinfz1.s
    reprval
    3sstr4d
    wph
    cA
    @3
    cS
    cN
    reprinfz1.a
    @51
    reprinfz1.s
    @55
    reprss
    eqssd
end
