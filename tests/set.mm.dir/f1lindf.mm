include "clmod.mm"
include "wcel.mm"
include "clindf.mm"
include "wbr.mm"
include "cdm.mm"
include "wf1.mm"
include "w3a.mm"
include "ccom.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "eqid.mm"
include "lindff.mm"
include "ancoms.mm"
include "3adant3.mm"
include "f1f.mm"
include "3ad2ant3.mm"
include "fco.mm"
include "syl2anc.mm"
include "wss.mm"
include "ffdm.mm"
include "simpld.mm"
include "syl.mm"
include "wa.mm"
include "wne.mm"
include "simpl2.mm"
include "adantr.mm"
include "wceq.mm"
include "fdm.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ffvelrnd.mm"
include "adantrr.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "eldifsni.mm"
include "lindfind.mm"
include "syl22anc.mm"
include "wi.mm"
include "wfn.mm"
include "f1fn.mm"
include "fvco2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "simpl1.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "imaco.mm"
include "difeq1d.mm"
include "imaeq2d.mm"
include "ccnv.mm"
include "wfun.mm"
include "df-f1.mm"
include "simprbi.mm"
include "imadif.mm"
include "eqtrd.mm"
include "fnsnfv.mm"
include "sylan.mm"
include "difeq2d.mm"
include "ssdifd.mm"
include "eqsstr3d.mm"
include "eqsstrd.mm"
include "imass2.mm"
include "syl5eqss.mm"
include "lspss.mm"
include "syl3anc.mm"
include "syldan.mm"
include "sseld.mm"
include "sylbid.mm"
include "mtod.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "simp1.mm"
include "rellindf.mm"
include "brrelexi.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "dmexg.mm"
include "f1dmex.mm"
include "fex.mm"
include "coexg.mm"
include "islindf.mm"
include "mpbir2and.mm"

theorem f1lindf
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. LMod /\ F LIndF W /\ G : K -1-1-> dom F ) -> ( F o. G ) LIndF W )

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
    cK
    cF
    cdm
    #
    cG
    wf1
    #
    w3a
    #
    cF
    cG
    ccom
    #
    cW
    clindf
    wbr
    #
    @5
    cdm
    #
    cW
    cbs
    cfv
    #
    @5
    wf
    #
    vk
    cv
    #
    vx
    cv
    #
    @5
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @5
    @7
    @11
    csn
    #
    cdif
    #
    cima
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
    @22
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    vx
    @7
    wral
    #
    @4
    cK
    @8
    @5
    wf
    #
    @9
    @4
    @2
    @8
    cF
    wf
    #
    cK
    @2
    cG
    wf
    #
    @28
    @0
    @1
    @29
    @3
    @1
    @0
    @29
    @8
    cF
    cW
    clmod
    @8
    eqid
    #
    lindff
    ancoms
    3adant3
    #
    @3
    @0
    @30
    @1
    cK
    @2
    cG
    f1f
    3ad2ant3
    #
    cK
    @2
    @8
    cF
    cG
    fco
    syl2anc
    #
    @28
    @9
    @7
    cK
    wss
    cK
    @8
    @5
    ffdm
    simpld
    syl
    @4
    @21
    vx
    vk
    @7
    @26
    @4
    @11
    @7
    wcel
    #
    @10
    @26
    wcel
    #
    wa
    #
    wa
    #
    @20
    @10
    @11
    cG
    cfv
    #
    cF
    cfv
    #
    @13
    co
    #
    cF
    @2
    @39
    csn
    #
    cdif
    #
    cima
    #
    @18
    cfv
    #
    wcel
    #
    @38
    @1
    @39
    @2
    wcel
    #
    @10
    @23
    wcel
    #
    @10
    @24
    wne
    #
    @46
    wn
    @0
    @1
    @3
    @37
    simpl2
    @4
    @35
    @47
    @36
    @4
    @35
    wa
    #
    cK
    @2
    @11
    cG
    @4
    @30
    @35
    @33
    adantr
    @4
    @35
    @11
    cK
    wcel
    #
    @4
    @7
    cK
    @11
    @4
    @28
    @7
    cK
    wceq
    @34
    cK
    @8
    @5
    fdm
    syl
    #
    eleq2d
    biimpa
    #
    ffvelrnd
    adantrr
    @36
    @48
    @4
    @35
    @10
    @23
    @25
    eldifi
    ad2antll
    @36
    @49
    @4
    @35
    @10
    @23
    @24
    eldifsni
    ad2antll
    @10
    @13
    @39
    cF
    @23
    @22
    @18
    cW
    @24
    @13
    eqid
    #
    @18
    eqid
    #
    @22
    eqid
    #
    @24
    eqid
    #
    @23
    eqid
    #
    lindfind
    syl22anc
    @4
    @35
    @20
    @46
    wi
    @36
    @50
    @20
    @41
    @19
    wcel
    @46
    @50
    @14
    @41
    @19
    @50
    @12
    @40
    @10
    @13
    @50
    cG
    cK
    wfn
    #
    @51
    @12
    @40
    wceq
    @4
    @59
    @35
    @3
    @0
    @59
    @1
    cK
    @2
    cG
    f1fn
    3ad2ant3
    #
    adantr
    @53
    cK
    cF
    cG
    @11
    fvco2
    syl2anc
    oveq2d
    eleq1d
    @50
    @19
    @45
    @41
    @4
    @35
    @51
    @19
    @45
    wss
    #
    @53
    @4
    @51
    wa
    #
    @0
    @44
    @8
    wss
    #
    @17
    @44
    wss
    @61
    @0
    @1
    @3
    @51
    simpl1
    @4
    @63
    @51
    @4
    @44
    cF
    crn
    #
    @8
    cF
    @43
    imassrn
    @4
    @29
    @64
    @8
    wss
    @32
    @2
    @8
    cF
    frn
    syl
    syl5ss
    adantr
    @62
    @17
    cF
    cG
    @16
    cima
    #
    cima
    #
    @44
    cF
    cG
    @16
    imaco
    @62
    @65
    @43
    wss
    @66
    @44
    wss
    @62
    @65
    cG
    cK
    cima
    #
    cG
    @15
    cima
    #
    cdif
    #
    @43
    @4
    @65
    @69
    wceq
    @51
    @4
    @65
    cG
    cK
    @15
    cdif
    #
    cima
    #
    @69
    @4
    @16
    @70
    cG
    @4
    @7
    cK
    @15
    @52
    difeq1d
    imaeq2d
    @4
    cG
    ccnv
    wfun
    #
    @71
    @69
    wceq
    @3
    @0
    @72
    @1
    @3
    @30
    @72
    cK
    @2
    cG
    df-f1
    simprbi
    3ad2ant3
    cK
    @15
    cG
    imadif
    syl
    eqtrd
    adantr
    @62
    @69
    @67
    @42
    cdif
    @43
    @62
    @42
    @68
    @67
    @4
    @59
    @51
    @42
    @68
    wceq
    @60
    cK
    @11
    cG
    fnsnfv
    sylan
    difeq2d
    @62
    @67
    @2
    @42
    @62
    @67
    cG
    crn
    #
    @2
    cG
    cK
    imassrn
    @62
    @30
    @73
    @2
    wss
    @4
    @30
    @51
    @33
    adantr
    cK
    @2
    cG
    frn
    syl
    syl5ss
    ssdifd
    eqsstr3d
    eqsstrd
    @65
    @43
    cF
    imass2
    syl
    syl5eqss
    @17
    @44
    @18
    @8
    cW
    @31
    @55
    lspss
    syl3anc
    syldan
    sseld
    sylbid
    adantrr
    mtod
    ralrimivva
    @4
    @0
    @5
    cvv
    wcel
    #
    @6
    @9
    @27
    wa
    wb
    @0
    @1
    @3
    simp1
    @4
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    @74
    @1
    @0
    @75
    @3
    cF
    cW
    clindf
    rellindf
    brrelexi
    3ad2ant2
    #
    @4
    @30
    cK
    cvv
    wcel
    #
    @76
    @33
    @4
    @3
    @2
    cvv
    wcel
    #
    @78
    @0
    @1
    @3
    simp3
    @4
    @75
    @79
    @77
    cF
    cvv
    dmexg
    syl
    cK
    @2
    cvv
    cG
    f1dmex
    syl2anc
    cK
    @2
    cvv
    cG
    fex
    syl2anc
    cF
    cG
    cvv
    cvv
    coexg
    syl2anc
    vx
    @8
    @22
    @13
    vk
    @5
    @18
    @23
    cW
    cvv
    clmod
    @24
    @31
    @54
    @55
    @56
    @58
    @57
    islindf
    syl2anc
    mpbir2and
end
