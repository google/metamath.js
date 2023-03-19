include "clgam.mm"
include "cfv.mm"
include "ce.mm"
include "cgam.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "ccxp.mm"
include "cprod.mm"
include "cc.mm"
include "cz.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "eflgam.mm"
include "syl.mm"
include "clog.mm"
include "cmul.mm"
include "cmin.mm"
include "csu.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "sumeq2sdv.mm"
include "fveq2.mm"
include "df-lgam.mm"
include "ovex.mm"
include "fvmpt.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "weq.mm"
include "id.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "eqid.mm"
include "adantl.mm"
include "wa.mm"
include "eldifad.mm"
include "adantr.mm"
include "peano2nn.mm"
include "nncnd.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcld.mm"
include "nnne0d.mm"
include "divne0d.mm"
include "logcld.mm"
include "mulcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "simpr.mm"
include "dmgmdivn0.mm"
include "subcld.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cdm.mm"
include "lgamcvg.mm"
include "seqex.mm"
include "breldm.mm"
include "isumcl.mm"
include "dmgmn0.mm"
include "efsub.mm"
include "syl2anc.mm"
include "iprodefisum.mm"
include "divdird.mm"
include "dividd.mm"
include "eqtrd.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpaddcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "cxpefd.mm"
include "eqtr4d.mm"
include "eflog.mm"
include "addcomd.mm"
include "prodeq2dv.mm"
include "eqtr3d.mm"

theorem iprodgam
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vj: setvar j
  let vz: setvar z
  assume iprodgam.1: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )

  disjoint A k
  disjoint k ph
  disjoint A j
  disjoint A z
  disjoint j k
  disjoint j ph
  disjoint k z
  assert |- ( ph -> ( _G ` A ) = ( prod_ k e. NN ( ( ( 1 + ( 1 / k ) ) ^c A ) / ( 1 + ( A / k ) ) ) / A ) )

  proof
    wph
    cA
    clgam
    cfv
    #
    ce
    cfv
    #
    cA
    cgam
    cfv
    #
    cn
    c1
    c1
    vk
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cA
    ccxp
    co
    #
    c1
    cA
    @3
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    vk
    cprod
    #
    cA
    cdiv
    co
    #
    wph
    cA
    cc
    cz
    cn
    cdif
    #
    cdif
    #
    wcel
    #
    @1
    @2
    wceq
    iprodgam.1
    cA
    eflgam
    syl
    wph
    @1
    cn
    cA
    @3
    c1
    caddc
    co
    #
    @3
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @7
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    vk
    csu
    #
    cA
    clog
    cfv
    #
    cmin
    co
    #
    ce
    cfv
    #
    @11
    wph
    @0
    @24
    ce
    wph
    @14
    @0
    @24
    wceq
    iprodgam.1
    vz
    cA
    cn
    vz
    cv
    #
    @17
    cmul
    co
    #
    @26
    @3
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    vk
    csu
    #
    @26
    clog
    cfv
    #
    cmin
    co
    @24
    @13
    clgam
    @26
    cA
    wceq
    #
    @32
    @22
    @33
    @23
    cmin
    @34
    cn
    @31
    @21
    vk
    @34
    @27
    @18
    @30
    @20
    cmin
    @26
    cA
    @17
    cmul
    oveq1
    @34
    @29
    @19
    clog
    @34
    @28
    @7
    c1
    caddc
    @26
    cA
    @3
    cdiv
    oveq1
    oveq1d
    fveq2d
    oveq12d
    sumeq2sdv
    @26
    cA
    clog
    fveq2
    oveq12d
    vz
    vk
    df-lgam
    @22
    @23
    cmin
    ovex
    fvmpt
    syl
    fveq2d
    wph
    @25
    @22
    ce
    cfv
    #
    @23
    ce
    cfv
    #
    cdiv
    co
    #
    @11
    wph
    @22
    cc
    wcel
    @23
    cc
    wcel
    @25
    @37
    wceq
    wph
    @21
    vk
    vj
    cn
    cA
    vj
    cv
    #
    c1
    caddc
    co
    #
    @38
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cA
    @38
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    wph
    1zzd
    #
    @3
    cn
    wcel
    #
    @3
    @47
    cfv
    @21
    wceq
    wph
    vj
    @3
    @46
    @21
    cn
    @47
    vj
    vk
    weq
    #
    @42
    @18
    @45
    @20
    cmin
    @50
    @41
    @17
    cA
    cmul
    @50
    @40
    @16
    clog
    @50
    @39
    @15
    @38
    @3
    cdiv
    @38
    @3
    c1
    caddc
    oveq1
    @50
    id
    oveq12d
    fveq2d
    oveq2d
    @50
    @44
    @19
    clog
    @50
    @43
    @7
    c1
    caddc
    @38
    @3
    cA
    cdiv
    oveq2
    oveq1d
    fveq2d
    oveq12d
    @47
    eqid
    #
    @18
    @20
    cmin
    ovex
    fvmpt
    adantl
    #
    wph
    @49
    wa
    #
    @18
    @20
    @53
    cA
    @17
    wph
    cA
    cc
    wcel
    #
    @49
    wph
    cA
    cc
    @12
    iprodgam.1
    eldifad
    #
    adantr
    #
    @53
    @16
    @53
    @15
    @3
    @53
    @15
    @49
    @15
    cn
    wcel
    wph
    @3
    peano2nn
    adantl
    #
    nncnd
    #
    @49
    @3
    cc
    wcel
    wph
    @3
    nncn
    adantl
    #
    @49
    @3
    cc0
    wne
    wph
    @3
    nnne0
    adantl
    #
    divcld
    @53
    @15
    @3
    @58
    @59
    @53
    @15
    @57
    nnne0d
    @60
    divne0d
    logcld
    mulcld
    #
    @53
    @19
    @53
    @7
    c1
    @53
    cA
    @3
    @56
    @59
    @60
    divcld
    #
    @53
    1cnd
    #
    addcld
    #
    @53
    cA
    @3
    wph
    @14
    @49
    iprodgam.1
    adantr
    wph
    @49
    simpr
    #
    dmgmdivn0
    #
    logcld
    #
    subcld
    #
    wph
    caddc
    @47
    c1
    cseq
    #
    @0
    @23
    caddc
    co
    #
    cli
    wbr
    @69
    cli
    cdm
    wcel
    wph
    cA
    vj
    @47
    @51
    iprodgam.1
    lgamcvg
    @69
    @70
    cli
    caddc
    @47
    c1
    seqex
    @0
    @23
    caddc
    ovex
    breldm
    syl
    #
    isumcl
    wph
    cA
    @55
    wph
    cA
    iprodgam.1
    dmgmn0
    #
    logcld
    @22
    @23
    efsub
    syl2anc
    wph
    @35
    @10
    @36
    cA
    cdiv
    wph
    cn
    @21
    ce
    cfv
    #
    vk
    cprod
    @35
    @10
    wph
    @21
    vk
    @47
    c1
    cn
    nnuz
    @48
    @52
    @68
    @71
    iprodefisum
    wph
    cn
    @73
    @9
    vk
    @53
    @73
    @18
    ce
    cfv
    #
    @20
    ce
    cfv
    #
    cdiv
    co
    #
    @9
    @53
    @18
    cc
    wcel
    @20
    cc
    wcel
    @73
    @76
    wceq
    @61
    @67
    @18
    @20
    efsub
    syl2anc
    @53
    @74
    @6
    @75
    @8
    cdiv
    @53
    @74
    cA
    @5
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    @6
    @53
    @18
    @78
    ce
    @53
    @17
    @77
    cA
    cmul
    @53
    @16
    @5
    clog
    @53
    @16
    @3
    @3
    cdiv
    co
    #
    @4
    caddc
    co
    @5
    @53
    @3
    c1
    @3
    @59
    @63
    @59
    @60
    divdird
    @53
    @79
    c1
    @4
    caddc
    @53
    @3
    @59
    @60
    dividd
    oveq1d
    eqtrd
    fveq2d
    oveq2d
    fveq2d
    @53
    @5
    cA
    @53
    @5
    @53
    c1
    @4
    c1
    crp
    wcel
    @53
    1rp
    a1i
    @53
    @3
    @53
    @3
    @65
    nnrpd
    rpreccld
    rpaddcld
    #
    rpcnd
    @53
    @5
    @80
    rpne0d
    @56
    cxpefd
    eqtr4d
    @53
    @75
    @19
    @8
    @53
    @19
    cc
    wcel
    @19
    cc0
    wne
    @75
    @19
    wceq
    @64
    @66
    @19
    eflog
    syl2anc
    @53
    @7
    c1
    @62
    @63
    addcomd
    eqtrd
    oveq12d
    eqtrd
    prodeq2dv
    eqtr3d
    wph
    @54
    cA
    cc0
    wne
    @36
    cA
    wceq
    @55
    @72
    cA
    eflog
    syl2anc
    oveq12d
    eqtrd
    eqtrd
    eqtr3d
end
