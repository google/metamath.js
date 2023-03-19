include "clmod.mm"
include "wcel.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "crn.mm"
include "clinds.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "wn.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "cdm.mm"
include "wf.mm"
include "eqid.mm"
include "lindff.mm"
include "ancoms.mm"
include "frn.mm"
include "syl.mm"
include "cima.mm"
include "simpll.mm"
include "imassrn.mm"
include "syl5ss.mm"
include "adantr.mm"
include "wfun.mm"
include "ffun.mm"
include "wne.mm"
include "eldifsn.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wb.mm"
include "wfn.mm"
include "funfn.mm"
include "fvelrnb.mm"
include "sylbi.mm"
include "difss.mm"
include "jctr.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "fveq2.mm"
include "necon3i.mm"
include "adantl.mm"
include "sylanbrc.mm"
include "funfvima2.mm"
include "sylc.mm"
include "expr.mm"
include "neeq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "impd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "sylan.mm"
include "lspss.mm"
include "syl3anc.mm"
include "adantrr.mm"
include "simplr.mm"
include "simprl.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "eldifsni.mm"
include "lindfind.mm"
include "syl22anc.mm"
include "ssneldd.mm"
include "ralrimivva.mm"
include "sylib.mm"
include "oveq2.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "ralrn.mm"
include "mpbird.mm"
include "islinds2.mm"
include "mpbir2and.mm"

theorem lindfrn
  let cF: class F
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( W e. LMod /\ F LIndF W ) -> ran F e. ( LIndS ` W ) )

  proof
    cW
    clmod
    wcel
    #
    cF
    cW
    clindf
    wbr
    #
    wa
    #
    cF
    crn
    #
    cW
    clinds
    cfv
    wcel
    #
    @3
    cW
    cbs
    cfv
    #
    wss
    #
    vk
    cv
    #
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @3
    @8
    csn
    #
    cdif
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @17
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    @3
    wral
    #
    @2
    cF
    cdm
    #
    @5
    cF
    wf
    #
    @6
    @1
    @0
    @25
    @5
    cF
    cW
    clmod
    @5
    eqid
    #
    lindff
    ancoms
    #
    @24
    @5
    cF
    frn
    syl
    #
    @2
    @23
    @7
    vy
    cv
    #
    cF
    cfv
    #
    @9
    co
    #
    @3
    @30
    csn
    #
    cdif
    #
    @13
    cfv
    #
    wcel
    #
    wn
    #
    vk
    @21
    wral
    #
    vy
    @24
    wral
    #
    @2
    @36
    vy
    vk
    @24
    @21
    @2
    @29
    @24
    wcel
    #
    @7
    @21
    wcel
    #
    wa
    #
    wa
    #
    @34
    cF
    @24
    @29
    csn
    #
    cdif
    #
    cima
    #
    @13
    cfv
    #
    @31
    @2
    @39
    @34
    @46
    wss
    #
    @40
    @2
    @39
    wa
    @0
    @45
    @5
    wss
    #
    @33
    @45
    wss
    #
    @47
    @0
    @1
    @39
    simpll
    @2
    @48
    @39
    @2
    @45
    @3
    @5
    cF
    @44
    imassrn
    @28
    syl5ss
    adantr
    @2
    cF
    wfun
    #
    @39
    @49
    @2
    @25
    @50
    @27
    @24
    @5
    cF
    ffun
    syl
    #
    @50
    @39
    wa
    #
    vx
    @33
    @45
    @8
    @33
    wcel
    @8
    @3
    wcel
    #
    @8
    @30
    wne
    #
    wa
    @52
    @8
    @45
    wcel
    #
    @8
    @3
    @30
    eldifsn
    @52
    @53
    @54
    @55
    @52
    @53
    @7
    cF
    cfv
    #
    @8
    wceq
    #
    vk
    @24
    wrex
    #
    @54
    @55
    wi
    #
    @50
    @53
    @58
    wb
    #
    @39
    @50
    cF
    @24
    wfn
    #
    @60
    cF
    funfn
    #
    vk
    @24
    @8
    cF
    fvelrnb
    sylbi
    adantr
    @52
    @57
    @59
    vk
    @24
    @52
    @7
    @24
    wcel
    #
    wa
    @56
    @30
    wne
    #
    @56
    @45
    wcel
    #
    wi
    @57
    @59
    @52
    @63
    @64
    @65
    @52
    @63
    @64
    wa
    #
    wa
    @50
    @44
    @24
    wss
    #
    wa
    #
    @7
    @44
    wcel
    #
    @65
    @50
    @68
    @39
    @66
    @50
    @67
    @24
    @43
    difss
    jctr
    ad2antrr
    @66
    @69
    @52
    @66
    @63
    @7
    @29
    wne
    #
    @69
    @63
    @64
    simpl
    @64
    @70
    @63
    @7
    @29
    @56
    @30
    @7
    @29
    cF
    fveq2
    necon3i
    adantl
    @7
    @24
    @29
    eldifsn
    sylanbrc
    adantl
    @44
    @7
    cF
    funfvima2
    sylc
    expr
    @57
    @64
    @54
    @65
    @55
    @56
    @8
    @30
    neeq1
    @56
    @8
    @45
    eleq1
    imbi12d
    syl5ibcom
    rexlimdva
    sylbid
    impd
    syl5bi
    ssrdv
    sylan
    @33
    @45
    @13
    @5
    cW
    @26
    @13
    eqid
    #
    lspss
    syl3anc
    adantrr
    @42
    @1
    @39
    @7
    @18
    wcel
    #
    @7
    @19
    wne
    #
    @31
    @46
    wcel
    wn
    @0
    @1
    @41
    simplr
    @2
    @39
    @40
    simprl
    @40
    @72
    @2
    @39
    @7
    @18
    @20
    eldifi
    ad2antll
    @40
    @73
    @2
    @39
    @7
    @18
    @19
    eldifsni
    ad2antll
    @7
    @9
    @29
    cF
    @18
    @17
    @13
    cW
    @19
    @9
    eqid
    #
    @71
    @17
    eqid
    #
    @19
    eqid
    #
    @18
    eqid
    #
    lindfind
    syl22anc
    ssneldd
    ralrimivva
    @2
    @61
    @23
    @38
    wb
    @2
    @50
    @61
    @51
    @62
    sylib
    @22
    @37
    vx
    vy
    @24
    cF
    @8
    @30
    wceq
    #
    @16
    @36
    vk
    @21
    @78
    @15
    @35
    @78
    @10
    @31
    @14
    @34
    @8
    @30
    @7
    @9
    oveq2
    @78
    @12
    @33
    @13
    @78
    @11
    @32
    @3
    @8
    @30
    sneq
    difeq2d
    fveq2d
    eleq12d
    notbid
    ralbidv
    ralrn
    syl
    mpbird
    @0
    @4
    @6
    @23
    wa
    wb
    @1
    vx
    @5
    @17
    @9
    vk
    @3
    @13
    @18
    cW
    clmod
    @19
    @26
    @74
    @71
    @75
    @77
    @76
    islinds2
    adantr
    mpbir2and
end
