include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "csu.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "cr.mm"
include "csn.mm"
include "cxp.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cfv.mm"
include "wceq.mm"
include "1ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "wa.mm"
include "1red.mm"
include "caddc.mm"
include "cseq.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "cdiv.mm"
include "co.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "nnrecre.mm"
include "eqeltrd.mm"
include "cle.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "breqtrrd.mm"
include "nnre.mm"
include "lep1d.mm"
include "wb.mm"
include "nngt0.mm"
include "peano2re.mm"
include "syl.mm"
include "peano2nn.mm"
include "nngt0d.mm"
include "lerec.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "3brtr4d.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "oveq2d.mm"
include "nncn.mm"
include "nnne0.mm"
include "recidd.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "climcnds.mm"
include "isumrecl.mm"
include "arch.mm"
include "wn.mm"
include "cfz.mm"
include "chash.mm"
include "cfn.mm"
include "cc.mm"
include "fzfid.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "wss.mm"
include "elfznn.mm"
include "ssriv.mm"
include "a1i.mm"
include "0le1.mm"
include "adantr.mm"
include "isumless.mm"
include "eqbrtrrd.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "nrexdv.mm"
include "pm2.65i.mm"

theorem harmonic
  let vn: setvar n
  let cF: class F
  let cH: class H
  let vk: setvar k
  let vj: setvar j
  assume harmonic.1: |- F = ( n e. NN |-> ( 1 / n ) )
  assume harmonic.2: |- H = seq 1 ( + , F )


  assert |- -. H e. dom ~~>

  proof
    cH
    cli
    cdm
    #
    wcel
    #
    cn0
    c1
    vk
    csu
    #
    vj
    cv
    #
    clt
    wbr
    #
    vj
    cn
    wrex
    #
    @1
    @2
    cr
    wcel
    #
    @5
    @1
    c1
    vk
    cn0
    c1
    csn
    cxp
    #
    cc0
    cn0
    nn0uz
    @1
    0zd
    vk
    cv
    #
    cn0
    wcel
    #
    @8
    @7
    cfv
    c1
    wceq
    #
    @1
    cn0
    c1
    @8
    1ex
    fvconst2
    #
    adantl
    @1
    @9
    wa
    1red
    @1
    caddc
    cF
    c1
    cseq
    #
    @0
    wcel
    #
    caddc
    @7
    cc0
    cseq
    @0
    wcel
    #
    @1
    @13
    cH
    @12
    @0
    harmonic.2
    eleq1i
    biimpi
    @1
    vk
    vj
    cF
    @7
    @8
    cn
    wcel
    #
    @8
    cF
    cfv
    #
    cr
    wcel
    @1
    @15
    @16
    c1
    @8
    cdiv
    co
    #
    cr
    vn
    @8
    c1
    vn
    cv
    #
    cdiv
    co
    #
    @17
    cn
    cF
    @18
    @8
    c1
    cdiv
    oveq2
    harmonic.1
    c1
    @8
    cdiv
    ovex
    fvmpt
    #
    @8
    nnrecre
    eqeltrd
    adantl
    @15
    cc0
    @16
    cle
    wbr
    @1
    @15
    cc0
    @17
    @16
    cle
    @15
    @17
    @15
    @8
    @8
    nnrp
    rpreccld
    rpge0d
    @20
    breqtrrd
    adantl
    @15
    @8
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @16
    cle
    wbr
    @1
    @15
    c1
    @21
    cdiv
    co
    #
    @17
    @22
    @16
    cle
    @15
    @8
    @21
    cle
    wbr
    #
    @23
    @17
    cle
    wbr
    #
    @15
    @8
    @8
    nnre
    #
    lep1d
    @15
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    @21
    cr
    wcel
    #
    cc0
    @21
    clt
    wbr
    @24
    @25
    wb
    @26
    @8
    nngt0
    @15
    @27
    @28
    @26
    @8
    peano2re
    syl
    @15
    @21
    @8
    peano2nn
    #
    nngt0d
    @8
    @21
    lerec
    syl22anc
    mpbid
    @15
    @21
    cn
    wcel
    @22
    @23
    wceq
    @29
    vn
    @21
    @19
    @23
    cn
    cF
    @18
    @21
    c1
    cdiv
    oveq2
    harmonic.1
    c1
    @21
    cdiv
    ovex
    fvmpt
    syl
    @20
    3brtr4d
    adantl
    @3
    cn0
    wcel
    #
    @3
    @7
    cfv
    c2
    @3
    cexp
    co
    #
    @31
    cF
    cfv
    #
    cmul
    co
    #
    wceq
    @1
    vk
    @3
    c2
    @8
    cexp
    co
    #
    @34
    cF
    cfv
    #
    cmul
    co
    #
    @33
    cn0
    @7
    @8
    @3
    wceq
    #
    @34
    @31
    @35
    @32
    cmul
    @8
    @3
    c2
    cexp
    oveq2
    #
    @37
    @34
    @31
    cF
    @38
    fveq2d
    oveq12d
    @7
    vk
    cn0
    c1
    cmpt
    vk
    cn0
    @36
    cmpt
    vk
    cn0
    c1
    fconstmpt
    vk
    cn0
    @36
    c1
    @9
    @36
    @34
    c1
    @34
    cdiv
    co
    #
    cmul
    co
    #
    c1
    @9
    @35
    @39
    @34
    cmul
    @9
    @34
    cn
    wcel
    #
    @35
    @39
    wceq
    c2
    cn
    wcel
    @9
    @41
    2nn
    c2
    @8
    nnexpcl
    mpan
    #
    vn
    @34
    @19
    @39
    cn
    cF
    @18
    @34
    c1
    cdiv
    oveq2
    harmonic.1
    c1
    @34
    cdiv
    ovex
    fvmpt
    syl
    oveq2d
    @9
    @41
    @40
    c1
    wceq
    @42
    @41
    @34
    @34
    nncn
    @34
    nnne0
    recidd
    syl
    eqtrd
    mpteq2ia
    eqtr4i
    @31
    @32
    cmul
    ovex
    fvmpt
    adantl
    climcnds
    mpbid
    #
    isumrecl
    #
    @2
    vj
    arch
    syl
    @1
    @4
    vj
    cn
    @1
    @3
    cn
    wcel
    #
    wa
    #
    @3
    @2
    cle
    wbr
    #
    @4
    wn
    #
    @46
    c1
    @3
    cfz
    co
    #
    c1
    vk
    csu
    #
    @3
    @2
    cle
    @46
    @50
    @49
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @3
    c1
    cmul
    co
    @3
    @46
    @49
    cfn
    wcel
    c1
    cc
    wcel
    @50
    @52
    wceq
    @46
    c1
    @3
    fzfid
    #
    ax-1cn
    @49
    c1
    vk
    fsumconst
    sylancl
    @46
    @51
    @3
    c1
    cmul
    @46
    @30
    @51
    @3
    wceq
    @45
    @30
    @1
    @3
    nnnn0
    adantl
    @3
    hashfz1
    syl
    oveq1d
    @46
    @3
    @45
    @3
    cc
    wcel
    @1
    @3
    nncn
    adantl
    mulid1d
    3eqtrd
    @46
    @49
    c1
    vk
    @7
    cc0
    cn0
    nn0uz
    @46
    0zd
    @53
    @49
    cn0
    wss
    @46
    vk
    @49
    cn0
    @8
    @49
    wcel
    @15
    @9
    @8
    @3
    elfznn
    @8
    nnnn0
    syl
    ssriv
    a1i
    @9
    @10
    @46
    @11
    adantl
    @46
    @9
    wa
    #
    1red
    cc0
    c1
    cle
    wbr
    @54
    0le1
    a1i
    @1
    @14
    @45
    @43
    adantr
    isumless
    eqbrtrrd
    @45
    @3
    cr
    wcel
    @6
    @47
    @48
    wb
    @1
    @3
    nnre
    @44
    @3
    @2
    lenlt
    syl2anr
    mpbid
    nrexdv
    pm2.65i
end
