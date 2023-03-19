include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "cneg.mm"
include "cbits.mm"
include "cfv.mm"
include "csad.mm"
include "caddc.mm"
include "cuz.mm"
include "cin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "simpr.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "znegcld.mm"
include "sadadd.mm"
include "syl2anc.mm"
include "c0.mm"
include "cc0.mm"
include "zcnd.mm"
include "addcomd.mm"
include "negidd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "0bits.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "wss.mm"
include "bitsss.mm"
include "inss1.mm"
include "syl5ss.mm"
include "sadass.mm"
include "mp3an12i.mm"
include "cfzo.mm"
include "bitsmod.mm"
include "cun.mm"
include "fzouzdisj.mm"
include "ineq2i.mm"
include "inindi.mm"
include "in0.mm"
include "3eqtr3i.mm"
include "saddisj.mm"
include "indi.mm"
include "syl6eqr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzouzsplit.mm"
include "syl.mm"
include "syl5eq.mm"
include "syl5sseq.mm"
include "df-ss.mm"
include "sylib.mm"
include "oveq2d.mm"
include "sadid2.mm"
include "3eqtr3d.mm"
include "cmin.mm"
include "negsubd.mm"
include "subcld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "nnrpd.mm"
include "moddiffl.mm"
include "3eqtr2d.mm"

theorem bitsres
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ZZ /\ N e. NN0 ) -> ( ( bits ` A ) i^i ( ZZ>= ` N ) ) = ( bits ` ( ( |_ ` ( A / ( 2 ^ N ) ) ) x. ( 2 ^ N ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    c2
    cN
    cexp
    co
    #
    cmo
    co
    #
    cneg
    #
    cbits
    cfv
    #
    cA
    cbits
    cfv
    #
    csad
    co
    #
    @5
    cA
    caddc
    co
    #
    cbits
    cfv
    #
    @7
    cN
    cuz
    cfv
    #
    cin
    #
    cA
    @3
    cdiv
    co
    cfl
    cfv
    #
    @3
    cmul
    co
    #
    cbits
    cfv
    @2
    @5
    cz
    wcel
    #
    @0
    @8
    @10
    wceq
    @2
    @4
    @2
    @4
    @2
    cA
    @3
    @0
    @1
    simpl
    #
    @2
    c2
    cN
    c2
    cn
    wcel
    @2
    2nn
    a1i
    @0
    @1
    simpr
    #
    nnexpcld
    #
    zmodcld
    nn0zd
    #
    znegcld
    #
    @16
    @5
    cA
    sadadd
    syl2anc
    @2
    @6
    @4
    cbits
    cfv
    #
    csad
    co
    #
    @12
    csad
    co
    #
    c0
    @12
    csad
    co
    #
    @8
    @12
    @2
    @22
    c0
    @12
    csad
    @2
    @22
    @5
    @4
    caddc
    co
    #
    cbits
    cfv
    #
    c0
    @2
    @15
    @4
    cz
    wcel
    @22
    @26
    wceq
    @20
    @19
    @5
    @4
    sadadd
    syl2anc
    @2
    @26
    cc0
    cbits
    cfv
    c0
    @2
    @25
    cc0
    cbits
    @2
    @25
    @4
    @5
    caddc
    co
    cc0
    @2
    @5
    @4
    @2
    @5
    @20
    zcnd
    #
    @2
    @4
    @19
    zcnd
    #
    addcomd
    @2
    @4
    @28
    negidd
    eqtrd
    fveq2d
    0bits
    syl6eq
    eqtrd
    oveq1d
    @2
    @23
    @6
    @21
    @12
    csad
    co
    #
    csad
    co
    #
    @8
    @6
    cn0
    wss
    @21
    cn0
    wss
    @2
    @12
    cn0
    wss
    #
    @23
    @30
    wceq
    @5
    bitsss
    @4
    bitsss
    @2
    @12
    @7
    cn0
    @7
    @11
    inss1
    @7
    cn0
    wss
    @2
    cA
    bitsss
    #
    a1i
    #
    syl5ss
    #
    @6
    @21
    @12
    sadass
    mp3an12i
    @2
    @29
    @7
    @6
    csad
    @2
    @29
    @7
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    @12
    csad
    co
    #
    @7
    @2
    @21
    @36
    @12
    csad
    cN
    cA
    bitsmod
    oveq1d
    @2
    @37
    @7
    @35
    @11
    cun
    #
    cin
    #
    @7
    @2
    @37
    @36
    @12
    cun
    @39
    @2
    @36
    @12
    @2
    @36
    @7
    cn0
    @7
    @35
    inss1
    @33
    syl5ss
    @34
    @36
    @12
    cin
    #
    c0
    wceq
    @2
    @7
    @35
    @11
    cin
    #
    cin
    @7
    c0
    cin
    @40
    c0
    @41
    c0
    @7
    cc0
    cN
    fzouzdisj
    ineq2i
    @7
    @35
    @11
    inindi
    @7
    in0
    3eqtr3i
    a1i
    saddisj
    @7
    @35
    @11
    indi
    syl6eqr
    @2
    @7
    @38
    wss
    @39
    @7
    wceq
    @2
    cn0
    @7
    @38
    @32
    @2
    cn0
    cc0
    cuz
    cfv
    #
    @38
    nn0uz
    @2
    cN
    @42
    wcel
    @42
    @38
    wceq
    @2
    cN
    cn0
    @42
    @17
    nn0uz
    syl6eleq
    cc0
    cN
    fzouzsplit
    syl
    syl5eq
    syl5sseq
    @7
    @38
    df-ss
    sylib
    eqtrd
    eqtrd
    oveq2d
    eqtrd
    @2
    @31
    @24
    @12
    wceq
    @34
    @12
    sadid2
    syl
    3eqtr3d
    @2
    @9
    @14
    cbits
    @2
    @9
    cA
    @5
    caddc
    co
    #
    @14
    @2
    @5
    cA
    @27
    @2
    cA
    @16
    zcnd
    #
    addcomd
    @2
    @43
    cA
    @4
    cmin
    co
    #
    @45
    @3
    cdiv
    co
    #
    @3
    cmul
    co
    @14
    @2
    cA
    @4
    @44
    @28
    negsubd
    @2
    @45
    @3
    @2
    cA
    @4
    @44
    @28
    subcld
    @2
    @3
    @18
    nncnd
    @2
    @3
    @18
    nnne0d
    divcan1d
    @2
    @46
    @13
    @3
    cmul
    @2
    cA
    cr
    wcel
    @3
    crp
    wcel
    @46
    @13
    wceq
    @2
    cA
    @16
    zred
    @2
    @3
    @18
    nnrpd
    cA
    @3
    moddiffl
    syl2anc
    oveq1d
    3eqtr2d
    eqtrd
    fveq2d
    3eqtr3d
end
