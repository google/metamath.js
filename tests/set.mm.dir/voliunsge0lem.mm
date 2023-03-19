include "cv.mm"
include "cfv.mm"
include "cvol.mm"
include "cpnf.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wa.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nffv.mm"
include "nfeq1.mm"
include "wcel.mm"
include "w3a.mm"
include "cxr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "cdm.mm"
include "wf.mm"
include "volf.mm"
include "a1i.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "iunmbl.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "adantr.mm"
include "3adant3.mm"
include "cle.mm"
include "id.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "wbr.mm"
include "wss.mm"
include "ssiun2.mm"
include "adantl.mm"
include "volss.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "xrgepnfd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "cvv.mm"
include "nfre1.mm"
include "nfan.mm"
include "nnex.mm"
include "adantlr.mm"
include "simpr.mm"
include "sge0pnfmpt.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cr.mm"
include "ralnex.mm"
include "biimpri.mm"
include "wb.mm"
include "wne.mm"
include "necon3bi.mm"
include "ge0xrre.mm"
include "syl2anc.mm"
include "ex.mm"
include "wi.mm"
include "renepnf.mm"
include "neneqd.mm"
include "impbid.mm"
include "ralbidva.mm"
include "mpbid.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wdisj.mm"
include "nfra1.mm"
include "rspa.mm"
include "adantll.mm"
include "jca.mm"
include "ralrimi.mm"
include "voliun.mm"
include "c1.mm"
include "1zzd.mm"
include "nnuz.mm"
include "cico.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "0xr.mm"
include "pnfxr.mm"
include "rexrd.mm"
include "volge0.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "chvar.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "caddc.mm"
include "cseq.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "sge0seq.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem voliunsge0lem
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cG: class G
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume voliunsge0lem.s: |- S = seq 1 ( + , G )
  assume voliunsge0lem.g: |- G = ( n e. NN |-> ( vol ` ( E ` n ) ) )
  assume voliunsge0lem.e: |- ( ph -> E : NN --> dom vol )
  assume voliunsge0lem.d: |- ( ph -> Disj_ n e. NN ( E ` n ) )

  disjoint E n
  disjoint n ph
  disjoint E m
  disjoint m n
  disjoint m ph
  disjoint k x
  assert |- ( ph -> ( vol ` U_ n e. NN ( E ` n ) ) = ( sum^ ` ( n e. NN |-> ( vol ` ( E ` n ) ) ) ) )

  proof
    wph
    vn
    cv
    #
    cE
    cfv
    #
    cvol
    cfv
    #
    cpnf
    wceq
    #
    vn
    cn
    wrex
    #
    vn
    cn
    @1
    ciun
    #
    cvol
    cfv
    #
    vn
    cn
    @2
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wph
    @4
    wa
    #
    @6
    cpnf
    @8
    wph
    @4
    @6
    cpnf
    wceq
    #
    wph
    @3
    @11
    vn
    cn
    wph
    vn
    nfv
    #
    vn
    @6
    cpnf
    vn
    @5
    cvol
    vn
    cvol
    nfcv
    vn
    cn
    @1
    nfiu1
    nffv
    nfeq1
    wph
    @0
    cn
    wcel
    #
    @3
    @11
    wph
    @13
    @3
    w3a
    #
    @6
    wph
    @13
    @6
    cxr
    wcel
    #
    @3
    wph
    @15
    @13
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @6
    cc0
    cpnf
    iccssxr
    wph
    cvol
    cdm
    #
    @16
    @5
    cvol
    @17
    @16
    cvol
    wf
    #
    wph
    volf
    a1i
    wph
    @1
    @17
    wcel
    #
    vn
    cn
    wral
    @5
    @17
    wcel
    #
    wph
    @19
    vn
    cn
    wph
    cn
    @17
    @0
    cE
    voliunsge0lem.e
    ffvelrnda
    #
    ralrimiva
    @1
    vn
    iunmbl
    syl
    #
    ffvelrnd
    sseldi
    adantr
    3adant3
    @14
    cpnf
    @2
    @6
    cle
    @3
    wph
    cpnf
    @2
    wceq
    @13
    @3
    @2
    cpnf
    @3
    id
    #
    eqcomd
    3ad2ant3
    wph
    @13
    @2
    @6
    cle
    wbr
    #
    @3
    wph
    @13
    wa
    #
    @19
    @20
    @1
    @5
    wss
    #
    @24
    @21
    wph
    @20
    @13
    @22
    adantr
    @13
    @26
    wph
    vn
    cn
    @1
    ssiun2
    adantl
    @1
    @5
    volss
    syl3anc
    3adant3
    eqbrtrd
    xrgepnfd
    3exp
    rexlimd
    imp
    @10
    cn
    @2
    vn
    cvv
    wph
    @4
    vn
    @12
    @3
    vn
    cn
    nfre1
    nfan
    cn
    cvv
    wcel
    @10
    nnex
    a1i
    wph
    @13
    @2
    @16
    wcel
    #
    @4
    @25
    @17
    @16
    @1
    cvol
    @18
    @25
    volf
    a1i
    @21
    ffvelrnd
    #
    adantlr
    wph
    @4
    simpr
    sge0pnfmpt
    eqtr4d
    wph
    @4
    wn
    #
    @2
    cr
    wcel
    #
    vn
    cn
    wral
    #
    @9
    wph
    @29
    wa
    @3
    wn
    #
    vn
    cn
    wral
    #
    @31
    @29
    @33
    wph
    @33
    @29
    @3
    vn
    cn
    ralnex
    biimpri
    adantl
    wph
    @33
    @31
    wb
    @29
    wph
    @32
    @30
    vn
    cn
    @25
    @32
    @30
    @25
    @32
    @30
    @25
    @32
    wa
    @27
    @2
    cpnf
    wne
    #
    @30
    @25
    @27
    @32
    @28
    adantr
    @32
    @34
    @25
    @3
    @2
    cpnf
    @23
    necon3bi
    adantl
    @2
    ge0xrre
    syl2anc
    ex
    @30
    @32
    wi
    @25
    @30
    @2
    cpnf
    @2
    renepnf
    neneqd
    a1i
    impbid
    ralbidva
    adantr
    mpbid
    wph
    @31
    wa
    #
    @6
    cS
    crn
    cxr
    clt
    csup
    #
    @8
    @35
    @19
    @30
    wa
    #
    vn
    cn
    wral
    vn
    cn
    @1
    wdisj
    #
    @6
    @36
    wceq
    @35
    @37
    vn
    cn
    wph
    @31
    vn
    @12
    @30
    vn
    cn
    nfra1
    nfan
    #
    @35
    @13
    @37
    @35
    @13
    wa
    #
    @19
    @30
    wph
    @13
    @19
    @31
    @21
    adantlr
    @31
    @13
    @30
    wph
    @30
    vn
    cn
    rspa
    adantll
    #
    jca
    ex
    ralrimi
    wph
    @38
    @31
    voliunsge0lem.d
    adantr
    @1
    cS
    vn
    cG
    voliunsge0lem.s
    voliunsge0lem.g
    voliun
    syl2anc
    @35
    @7
    cS
    c1
    cn
    @35
    1zzd
    nnuz
    @35
    vm
    cn
    vm
    cv
    #
    cE
    cfv
    #
    cvol
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    @7
    @40
    @2
    @45
    wcel
    #
    wi
    @35
    @42
    cn
    wcel
    #
    wa
    #
    @44
    @45
    wcel
    #
    wi
    vn
    vm
    @48
    @49
    vn
    @35
    @47
    vn
    @39
    @47
    vn
    nfv
    nfan
    @49
    vn
    nfv
    nfim
    @0
    @42
    wceq
    #
    @40
    @48
    @46
    @49
    @50
    @13
    @47
    @35
    @0
    @42
    cn
    eleq1
    anbi2d
    @50
    @2
    @44
    @45
    @50
    @1
    @43
    cvol
    @0
    @42
    cE
    fveq2
    fveq2d
    #
    eleq1d
    imbi12d
    @40
    cc0
    cpnf
    @2
    cc0
    cxr
    wcel
    @40
    0xr
    a1i
    cpnf
    cxr
    wcel
    @40
    pnfxr
    a1i
    @40
    @2
    @41
    rexrd
    wph
    @13
    cc0
    @2
    cle
    wbr
    #
    @31
    @25
    @19
    @52
    @21
    @1
    volge0
    syl
    adantlr
    @40
    @2
    @41
    ltpnfd
    elicod
    chvar
    vn
    vm
    cn
    @2
    @44
    @51
    cbvmptv
    fmptd
    cS
    caddc
    cG
    c1
    cseq
    #
    caddc
    @7
    c1
    cseq
    #
    voliunsge0lem.s
    cG
    @7
    wceq
    @53
    @54
    wceq
    voliunsge0lem.g
    caddc
    cG
    @7
    c1
    seqeq3
    ax-mp
    eqtri
    sge0seq
    eqtr4d
    syldan
    pm2.61dan
end
