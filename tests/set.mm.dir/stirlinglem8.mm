include "c4.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cli.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nnuz.mm"
include "1zzd.mm"
include "crp.mm"
include "wf.mm"
include "cc.mm"
include "wss.mm"
include "rrpsscn.mm"
include "fss.mm"
include "sylancl.mm"
include "cn0.mm"
include "wcel.mm"
include "4nn0.mm"
include "a1i.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "ffvelrnda.mm"
include "rpcnd.mm"
include "expcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "climexp.mm"
include "cmul.mm"
include "adantr.mm"
include "2nn.mm"
include "id.mm"
include "nnmulcld.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "fmptdf.mm"
include "fex.mm"
include "1nn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "mulcld.mm"
include "oveq2.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "caddc.mm"
include "cuz.mm"
include "cle.mm"
include "wbr.mm"
include "1red.mm"
include "nnred.mm"
include "nnge1d.mm"
include "leadd2dd.mm"
include "mpdan.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "oveq2d.mm"
include "peano2nn.mm"
include "fvmptd.mm"
include "nncn.mm"
include "adddid.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "3brtr4d.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "eluz.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "climsuse.mm"
include "2nn0.mm"
include "sqcld.mm"
include "rpne0d.mm"
include "2z.mm"
include "expne0d.mm"
include "cc0.mm"
include "csn.mm"
include "eqeltrrd.mm"
include "rpexpcld.mm"
include "neneqd.mm"
include "0cn.mm"
include "elsn2g.mm"
include "ax-mp.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "nn0zd.mm"
include "rpdivcld.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "climdivf.mm"
include "cmin.mm"
include "2cn.mm"
include "2p2e4.mm"
include "mvlladdi.mm"
include "expsubd.mm"
include "breqtrrd.mm"

theorem stirlinglem8
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cL: class L
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume stirlinglem8.1: |- F/ n ph
  assume stirlinglem8.2: |- F/_ n A
  assume stirlinglem8.3: |- F/_ n D
  assume stirlinglem8.4: |- D = ( n e. NN |-> ( A ` ( 2 x. n ) ) )
  assume stirlinglem8.5: |- ( ph -> A : NN --> RR+ )
  assume stirlinglem8.6: |- F = ( n e. NN |-> ( ( ( A ` n ) ^ 4 ) / ( ( D ` n ) ^ 2 ) ) )
  assume stirlinglem8.7: |- L = ( n e. NN |-> ( ( A ` n ) ^ 4 ) )
  assume stirlinglem8.8: |- M = ( n e. NN |-> ( ( D ` n ) ^ 2 ) )
  assume stirlinglem8.9: |- ( ( ph /\ n e. NN ) -> ( D ` n ) e. RR+ )
  assume stirlinglem8.10: |- ( ph -> C e. RR+ )
  assume stirlinglem8.11: |- ( ph -> A ~~> C )


  assert |- ( ph -> F ~~> ( C ^ 2 ) )

  proof
    wph
    cF
    cC
    c4
    cexp
    co
    #
    cC
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @1
    cli
    wph
    @0
    @1
    vn
    cL
    cM
    cF
    c1
    cvv
    cn
    stirlinglem8.1
    vn
    cL
    vn
    cn
    vn
    cv
    #
    cA
    cfv
    #
    c4
    cexp
    co
    #
    cmpt
    #
    stirlinglem8.7
    vn
    cn
    @5
    nfmpt1
    nfcxfr
    #
    vn
    cM
    vn
    cn
    @3
    cD
    cfv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    stirlinglem8.8
    vn
    cn
    @9
    nfmpt1
    nfcxfr
    #
    vn
    cF
    vn
    cn
    @5
    @9
    cdiv
    co
    #
    cmpt
    #
    stirlinglem8.6
    vn
    cn
    @12
    nfmpt1
    nfcxfr
    nnuz
    wph
    1zzd
    #
    wph
    cC
    vn
    cA
    cL
    c1
    c4
    cvv
    cn
    stirlinglem8.1
    stirlinglem8.2
    @7
    nnuz
    @14
    wph
    cn
    crp
    cA
    wf
    crp
    cc
    wss
    cn
    cc
    cA
    wf
    #
    stirlinglem8.5
    rrpsscn
    cn
    crp
    cc
    cA
    fss
    sylancl
    #
    stirlinglem8.11
    c4
    cn0
    wcel
    #
    wph
    4nn0
    a1i
    #
    cL
    cvv
    wcel
    wph
    cL
    @6
    cvv
    stirlinglem8.7
    vn
    cn
    @5
    nnex
    mptex
    eqeltri
    a1i
    wph
    @3
    cn
    wcel
    #
    wa
    #
    @19
    @5
    cc
    wcel
    @3
    cL
    cfv
    #
    @5
    wceq
    #
    wph
    @19
    simpr
    #
    @20
    @4
    c4
    @20
    @4
    wph
    cn
    crp
    @3
    cA
    stirlinglem8.5
    ffvelrnda
    #
    rpcnd
    #
    @17
    @20
    4nn0
    a1i
    #
    expcld
    #
    vn
    cn
    @5
    cc
    cL
    stirlinglem8.7
    fvmpt2
    syl2anc
    climexp
    cF
    cvv
    wcel
    wph
    cF
    @13
    cvv
    stirlinglem8.6
    vn
    cn
    @12
    nnex
    mptex
    eqeltri
    a1i
    wph
    cC
    vn
    cD
    cM
    c1
    c2
    cvv
    cn
    stirlinglem8.1
    stirlinglem8.3
    @11
    nnuz
    @14
    wph
    vn
    cn
    c2
    @3
    cmul
    co
    #
    cA
    cfv
    #
    cc
    cD
    stirlinglem8.1
    @20
    cn
    cc
    @28
    cA
    wph
    @15
    @19
    @16
    adantr
    @19
    @28
    cn
    wcel
    #
    wph
    @19
    c2
    @3
    c2
    cn
    wcel
    #
    @19
    2nn
    a1i
    #
    @19
    id
    nnmulcld
    #
    adantl
    ffvelrnd
    #
    stirlinglem8.4
    fmptdf
    wph
    cC
    vn
    cA
    cD
    vn
    cn
    @28
    cmpt
    #
    c1
    cvv
    cvv
    cn
    stirlinglem8.1
    stirlinglem8.2
    stirlinglem8.3
    vn
    cn
    @28
    nfmpt1
    nnuz
    @14
    wph
    @15
    cn
    cvv
    wcel
    cA
    cvv
    wcel
    @16
    nnex
    cn
    cc
    cvv
    cA
    fex
    sylancl
    @25
    stirlinglem8.11
    wph
    c1
    @35
    cfv
    #
    c2
    c1
    cmul
    co
    #
    cn
    wph
    c1
    cn
    wcel
    #
    @37
    cc
    wcel
    @36
    @37
    wceq
    1nn
    wph
    c2
    c1
    wph
    2cnd
    wph
    1cnd
    mulcld
    vn
    c1
    @28
    @37
    cn
    cc
    @35
    @3
    c1
    c2
    cmul
    oveq2
    @35
    eqid
    #
    fvmptg
    sylancr
    wph
    c2
    c1
    @31
    wph
    2nn
    a1i
    @38
    wph
    1nn
    a1i
    nnmulcld
    eqeltrd
    @19
    @3
    c1
    caddc
    co
    #
    @35
    cfv
    #
    @3
    @35
    cfv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wph
    @19
    @44
    @43
    @41
    cle
    wbr
    #
    @19
    @28
    c1
    caddc
    co
    @28
    c2
    caddc
    co
    #
    @43
    @41
    cle
    @19
    c1
    c2
    @28
    @19
    1red
    @19
    c2
    @32
    nnred
    @19
    @28
    @33
    nnred
    @19
    c2
    @32
    nnge1d
    leadd2dd
    @19
    @42
    @28
    c1
    caddc
    @19
    @30
    @42
    @28
    wceq
    #
    @33
    vn
    cn
    @28
    cn
    @35
    @39
    fvmpt2
    mpdan
    #
    oveq1d
    @19
    @41
    c2
    @40
    cmul
    co
    #
    @28
    @37
    caddc
    co
    @46
    @19
    vk
    @40
    c2
    vk
    cv
    #
    cmul
    co
    #
    @49
    cn
    @35
    cn
    @35
    vk
    cn
    @51
    cmpt
    wceq
    @19
    vn
    vk
    cn
    @28
    @51
    @3
    @50
    c2
    cmul
    oveq2
    cbvmptv
    a1i
    @19
    @50
    @40
    wceq
    #
    wa
    @50
    @40
    c2
    cmul
    @19
    @52
    simpr
    oveq2d
    @3
    peano2nn
    #
    @19
    c2
    @40
    @32
    @53
    nnmulcld
    #
    fvmptd
    #
    @19
    c2
    @3
    c1
    @19
    2cnd
    #
    @3
    nncn
    @19
    1cnd
    adddid
    @19
    @37
    c2
    @28
    caddc
    @19
    c2
    @56
    mulid1d
    oveq2d
    3eqtrd
    3brtr4d
    @19
    @43
    cz
    wcel
    @41
    cz
    wcel
    @44
    @45
    wb
    @19
    @42
    @19
    @42
    @28
    cz
    @48
    @19
    @28
    @33
    nnzd
    eqeltrd
    peano2zd
    @19
    @41
    @49
    cz
    @55
    @19
    @49
    @54
    nnzd
    eqeltrd
    @43
    @41
    eluz
    syl2anc
    mpbird
    adantl
    cD
    cvv
    wcel
    wph
    cD
    vn
    cn
    @29
    cmpt
    cvv
    stirlinglem8.4
    vn
    cn
    @29
    nnex
    mptex
    eqeltri
    a1i
    @20
    @8
    @29
    @42
    cA
    cfv
    @20
    @19
    @29
    cc
    wcel
    @8
    @29
    wceq
    @23
    @34
    vn
    cn
    @29
    cc
    cD
    stirlinglem8.4
    fvmpt2
    syl2anc
    #
    @20
    @28
    @42
    cA
    @20
    @42
    @28
    @19
    @47
    wph
    @48
    adantl
    eqcomd
    fveq2d
    eqtrd
    climsuse
    c2
    cn0
    wcel
    wph
    2nn0
    a1i
    cM
    cvv
    wcel
    wph
    cM
    @10
    cvv
    stirlinglem8.8
    vn
    cn
    @9
    nnex
    mptex
    eqeltri
    a1i
    @20
    @19
    @9
    cc
    wcel
    @3
    cM
    cfv
    #
    @9
    wceq
    @23
    @20
    @8
    @20
    @8
    stirlinglem8.9
    rpcnd
    sqcld
    #
    vn
    cn
    @9
    cc
    cM
    stirlinglem8.8
    fvmpt2
    syl2anc
    #
    climexp
    wph
    cC
    c2
    wph
    cC
    stirlinglem8.10
    rpcnd
    #
    wph
    cC
    stirlinglem8.10
    rpne0d
    #
    c2
    cz
    wcel
    #
    wph
    2z
    a1i
    #
    expne0d
    wph
    cn
    cc
    @3
    cL
    wph
    vn
    cn
    @5
    cc
    cL
    stirlinglem8.1
    @27
    stirlinglem8.7
    fmptdf
    ffvelrnda
    @20
    @58
    cc
    cc0
    csn
    #
    @20
    @58
    @9
    cc
    @60
    @59
    eqeltrd
    @20
    @58
    cc0
    wceq
    #
    @58
    @65
    wcel
    #
    @20
    @58
    cc0
    @20
    @58
    @20
    @58
    @29
    c2
    cexp
    co
    #
    crp
    @20
    @58
    @9
    @68
    @60
    @20
    @8
    @29
    c2
    cexp
    @57
    oveq1d
    eqtrd
    @20
    @29
    c2
    @20
    @8
    @29
    crp
    @57
    stirlinglem8.9
    eqeltrrd
    @63
    @20
    2z
    a1i
    #
    rpexpcld
    eqeltrd
    rpne0d
    neneqd
    cc0
    cc
    wcel
    @67
    @66
    wb
    0cn
    @58
    cc0
    cc
    elsn2g
    ax-mp
    sylnibr
    eldifd
    @20
    @3
    cF
    cfv
    #
    @12
    @21
    @58
    cdiv
    co
    @20
    @19
    @12
    crp
    wcel
    @70
    @12
    wceq
    @23
    @20
    @5
    @9
    @20
    @4
    c4
    @24
    @20
    c4
    @26
    nn0zd
    rpexpcld
    #
    @20
    @8
    c2
    stirlinglem8.9
    @69
    rpexpcld
    rpdivcld
    vn
    cn
    @12
    crp
    cF
    stirlinglem8.6
    fvmpt2
    syl2anc
    @20
    @21
    @5
    @58
    @9
    cdiv
    @20
    @19
    @5
    crp
    wcel
    @22
    @23
    @71
    vn
    cn
    @5
    crp
    cL
    stirlinglem8.7
    fvmpt2
    syl2anc
    @60
    oveq12d
    eqtr4d
    climdivf
    wph
    @1
    cC
    c4
    c2
    cmin
    co
    #
    cexp
    co
    @2
    wph
    c2
    @72
    cC
    cexp
    c2
    @72
    wceq
    wph
    c2
    c2
    c4
    2cn
    2cn
    2p2e4
    mvlladdi
    a1i
    oveq2d
    wph
    cC
    c4
    c2
    @61
    @62
    @64
    wph
    c4
    @18
    nn0zd
    expsubd
    eqtrd
    breqtrrd
end
