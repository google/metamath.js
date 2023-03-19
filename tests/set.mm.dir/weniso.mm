include "wwe.mm"
include "wse.mm"
include "wiso.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wn.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "rabn0.mm"
include "rexnal.mm"
include "bitri.mm"
include "wbr.mm"
include "wa.mm"
include "wreu.mm"
include "wss.mm"
include "simpl1.mm"
include "simpl2.mm"
include "ssrab2.mm"
include "a1i.mm"
include "simpr.mm"
include "wereu2.mm"
include "syl22anc.mm"
include "reurex.mm"
include "syl.mm"
include "ex.mm"
include "wcel.mm"
include "wi.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "notbid.mm"
include "elrab.mm"
include "ralrab.mm"
include "con34b.mm"
include "bicomi.mm"
include "ralbii.mm"
include "wf1o.mm"
include "wf.mm"
include "simpl3.mm"
include "isof1o.mm"
include "f1of.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "breq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "imp.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "pm2.21.mm"
include "ad2antll.mm"
include "sylbid.mm"
include "adantr.mm"
include "syld.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "isorel.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "bitr2d.mm"
include "biimpa.mm"
include "sylc.mm"
include "simplrr.mm"
include "adantl.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "wo.mm"
include "simprr.mm"
include "wor.mm"
include "weso.mm"
include "sotrieq.mm"
include "con2bid.mm"
include "mpbird.mm"
include "mpjaodan.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "syl5bir.mm"
include "pm2.18d.mm"
include "fvresi.mm"
include "eqeq2d.mm"
include "biimprd.mm"
include "ralimia.mm"
include "wfn.mm"
include "3ad2ant3.mm"
include "f1ofn.mm"
include "fnresi.mm"
include "eqfnfv.mm"

theorem weniso
  let cA: class A
  let cR: class R
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( R We A /\ R Se A /\ F Isom R , R ( A , A ) ) -> F = ( _I |` A ) )

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    cA
    cA
    cR
    cR
    cF
    wiso
    #
    w3a
    #
    cF
    cid
    cA
    cres
    #
    wceq
    #
    va
    cv
    #
    cF
    cfv
    #
    @6
    @4
    cfv
    #
    wceq
    #
    va
    cA
    wral
    #
    @3
    @7
    @6
    wceq
    #
    va
    cA
    wral
    #
    @10
    @3
    @12
    @12
    wn
    #
    @11
    wn
    #
    va
    cA
    crab
    #
    c0
    wne
    #
    @3
    @12
    @16
    @14
    va
    cA
    wrex
    @13
    @14
    va
    cA
    rabn0
    @11
    va
    cA
    rexnal
    bitri
    @3
    @16
    vc
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    wn
    #
    vc
    @15
    wral
    #
    vb
    @15
    wrex
    #
    @12
    @3
    @16
    @22
    @3
    @16
    wa
    #
    @21
    vb
    @15
    wreu
    #
    @22
    @23
    @0
    @1
    @15
    cA
    wss
    #
    @16
    @24
    @0
    @1
    @2
    @16
    simpl1
    @0
    @1
    @2
    @16
    simpl2
    @25
    @23
    @14
    va
    cA
    ssrab2
    a1i
    @3
    @16
    simpr
    vb
    vc
    cA
    @15
    cR
    wereu2
    syl22anc
    @21
    vb
    @15
    reurex
    syl
    ex
    @3
    @21
    @12
    vb
    @15
    @18
    @15
    wcel
    @18
    cA
    wcel
    #
    @18
    cF
    cfv
    #
    @18
    wceq
    #
    wn
    #
    wa
    #
    @3
    @21
    @12
    wi
    #
    @14
    @29
    va
    @18
    cA
    @6
    @18
    wceq
    #
    @11
    @28
    @32
    @7
    @27
    @6
    @18
    @6
    @18
    cF
    fveq2
    @32
    id
    eqeq12d
    notbid
    elrab
    @3
    @30
    @31
    @21
    @19
    @17
    cF
    cfv
    #
    @17
    wceq
    #
    wi
    #
    vc
    cA
    wral
    #
    @3
    @30
    wa
    #
    @12
    @21
    @34
    wn
    #
    @20
    wi
    #
    vc
    cA
    wral
    @36
    @14
    @38
    @20
    vc
    va
    cA
    @6
    @17
    wceq
    #
    @11
    @34
    @40
    @7
    @33
    @6
    @17
    @6
    @17
    cF
    fveq2
    @40
    id
    eqeq12d
    notbid
    ralrab
    @39
    @35
    vc
    cA
    @35
    @39
    @19
    @34
    con34b
    bicomi
    ralbii
    bitri
    @37
    @27
    @18
    cR
    wbr
    #
    @36
    @12
    wi
    @18
    @27
    cR
    wbr
    #
    @37
    @41
    wa
    @36
    @27
    cF
    cfv
    #
    @27
    wceq
    #
    @12
    @37
    @41
    @36
    @44
    wi
    @37
    @36
    @41
    @44
    @37
    @27
    cA
    wcel
    #
    @36
    @41
    @44
    wi
    #
    wi
    @37
    cA
    cA
    @18
    cF
    @37
    cA
    cA
    cF
    wf1o
    #
    cA
    cA
    cF
    wf
    @37
    @2
    @47
    @0
    @1
    @2
    @30
    simpl3
    #
    cA
    cA
    cR
    cR
    cF
    isof1o
    #
    syl
    #
    cA
    cA
    cF
    f1of
    syl
    @3
    @26
    @29
    simprl
    #
    ffvelrnd
    #
    @35
    @46
    vc
    @27
    cA
    @17
    @27
    wceq
    #
    @19
    @41
    @34
    @44
    @17
    @27
    @18
    cR
    breq1
    @53
    @33
    @43
    @17
    @27
    @17
    @27
    cF
    fveq2
    @53
    id
    eqeq12d
    imbi12d
    rspcv
    syl
    com23
    imp
    @37
    @44
    @12
    wi
    @41
    @37
    @44
    @28
    @12
    @37
    cA
    cA
    cF
    wf1
    #
    @45
    @26
    @44
    @28
    wb
    @37
    @47
    @54
    @50
    cA
    cA
    cF
    f1of1
    syl
    @52
    @51
    cA
    cA
    @27
    @18
    cF
    f1fveq
    syl12anc
    @29
    @28
    @12
    wi
    @3
    @26
    @28
    @12
    pm2.21
    #
    ad2antll
    sylbid
    adantr
    syld
    @37
    @42
    wa
    #
    @36
    @18
    cF
    ccnv
    #
    cfv
    #
    cF
    cfv
    #
    @58
    wceq
    #
    @12
    @56
    @58
    cA
    wcel
    #
    @58
    @18
    cR
    wbr
    #
    @36
    @60
    wi
    @37
    @61
    @42
    @37
    cA
    cA
    @18
    @57
    @37
    @47
    cA
    cA
    @57
    wf1o
    cA
    cA
    @57
    wf
    @50
    cA
    cA
    cF
    f1ocnv
    cA
    cA
    @57
    f1of
    3syl
    @51
    ffvelrnd
    #
    adantr
    @37
    @42
    @62
    @37
    @62
    @59
    @27
    cR
    wbr
    #
    @42
    @37
    @2
    @61
    @26
    @62
    @64
    wb
    @48
    @63
    @51
    cA
    cA
    @58
    @18
    cR
    cR
    cF
    isorel
    syl12anc
    @37
    @59
    @18
    @27
    cR
    @37
    @47
    @26
    @59
    @18
    wceq
    #
    @50
    @51
    cA
    cA
    @18
    cF
    f1ocnvfv2
    syl2anc
    #
    breq1d
    bitr2d
    biimpa
    @61
    @36
    @62
    @60
    @35
    @62
    @60
    wi
    vc
    @58
    cA
    @17
    @58
    wceq
    #
    @19
    @62
    @34
    @60
    @17
    @58
    @18
    cR
    breq1
    @67
    @33
    @59
    @17
    @58
    @17
    @58
    cF
    fveq2
    @67
    id
    eqeq12d
    imbi12d
    rspcv
    com23
    sylc
    @37
    @60
    @12
    wi
    @42
    @37
    @60
    @12
    @37
    @60
    wa
    #
    @29
    @28
    @12
    @3
    @26
    @29
    @60
    simplrr
    @68
    @59
    cF
    cfv
    #
    @59
    @27
    @18
    @60
    @69
    @59
    wceq
    @37
    @59
    @58
    cF
    fveq2
    adantl
    @37
    @69
    @27
    wceq
    @60
    @37
    @59
    @18
    cF
    @66
    fveq2d
    adantr
    @37
    @65
    @60
    @66
    adantr
    3eqtr3d
    @55
    sylc
    ex
    adantr
    syld
    @37
    @41
    @42
    wo
    #
    @29
    @3
    @26
    @29
    simprr
    @37
    @28
    @70
    @37
    cA
    cR
    wor
    #
    @45
    @26
    @28
    @70
    wn
    wb
    @37
    @0
    @71
    @0
    @1
    @2
    @30
    simpl1
    cA
    cR
    weso
    syl
    @52
    @51
    cA
    @27
    @18
    cR
    sotrieq
    syl12anc
    con2bid
    mpbird
    mpjaodan
    syl5bi
    ex
    syl5bi
    rexlimdv
    syld
    syl5bir
    pm2.18d
    @11
    @9
    va
    cA
    @6
    cA
    wcel
    #
    @9
    @11
    @72
    @8
    @6
    @7
    cA
    @6
    fvresi
    eqeq2d
    biimprd
    ralimia
    syl
    @3
    cF
    cA
    wfn
    #
    @4
    cA
    wfn
    #
    @5
    @10
    wb
    @3
    @47
    @73
    @2
    @0
    @47
    @1
    @49
    3ad2ant3
    cA
    cA
    cF
    f1ofn
    syl
    @74
    @3
    cA
    fnresi
    a1i
    va
    cA
    cF
    @4
    eqfnfv
    syl2anc
    mpbird
end
