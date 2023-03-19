include "ccom.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "cvv.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "dprdgrp.mm"
include "syl.mm"
include "wf1.mm"
include "wf1o.mm"
include "f1of1.mm"
include "dprddomcld.mm"
include "f1dmex.mm"
include "syl2anc.mm"
include "wf.mm"
include "dprdf2.mm"
include "f1of.mm"
include "fco.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "adantr.mm"
include "simpr1.mm"
include "ffvelrnd.mm"
include "simpr2.mm"
include "simpr3.mm"
include "wb.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "dprdcntz.mm"
include "fvco3.mm"
include "fveq2d.mm"
include "3sstr4d.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "wss.mm"
include "sylan.mm"
include "imaco.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imadif.mm"
include "3syl.mm"
include "f1ofo.mm"
include "foima.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fnsnfv.mm"
include "eqcomd.mm"
include "difeq12d.mm"
include "eqtrd.mm"
include "imaeq2d.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "ineq12d.mm"
include "ffvelrnda.mm"
include "dprddisj.mm"
include "eqimss.mm"
include "dmdprdd.mm"
include "crn.mm"
include "rnco2.mm"
include "forn.mm"
include "ffn.mm"
include "fnima.mm"
include "dprdspan.mm"
include "3eqtr4d.mm"
include "jca.mm"

theorem dprdf1o
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  assume dprdf1o.1: |- ( ph -> G dom DProd S )
  assume dprdf1o.2: |- ( ph -> dom S = I )
  assume dprdf1o.3: |- ( ph -> F : J -1-1-onto-> I )


  assert |- ( ph -> ( G dom DProd ( S o. F ) /\ ( G DProd ( S o. F ) ) = ( G DProd S ) ) )

  proof
    wph
    cG
    cS
    cF
    ccom
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @0
    cdprd
    co
    #
    cG
    cS
    cdprd
    co
    #
    wceq
    wph
    vx
    vy
    @0
    cG
    cJ
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cvv
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    @8
    eqid
    #
    @7
    eqid
    #
    @6
    eqid
    #
    wph
    cG
    cS
    @1
    wbr
    #
    cG
    cgrp
    wcel
    dprdf1o.1
    cS
    cG
    dprdgrp
    syl
    wph
    cJ
    cI
    cF
    wf1
    #
    cI
    cvv
    wcel
    cJ
    cvv
    wcel
    wph
    cJ
    cI
    cF
    wf1o
    #
    @13
    dprdf1o.3
    cJ
    cI
    cF
    f1of1
    syl
    #
    wph
    cS
    cG
    cI
    dprdf1o.1
    dprdf1o.2
    dprddomcld
    cJ
    cI
    cvv
    cF
    f1dmex
    syl2anc
    wph
    cI
    @5
    cS
    wf
    #
    cJ
    cI
    cF
    wf
    #
    cJ
    @5
    @0
    wf
    wph
    cS
    cG
    cI
    dprdf1o.1
    dprdf1o.2
    dprdf2
    #
    wph
    @14
    @17
    dprdf1o.3
    cJ
    cI
    cF
    f1of
    syl
    #
    cJ
    cI
    @5
    cS
    cF
    fco
    syl2anc
    wph
    vx
    cv
    #
    cJ
    wcel
    #
    vy
    cv
    #
    cJ
    wcel
    #
    @20
    @22
    wne
    #
    w3a
    #
    wa
    #
    @20
    cF
    cfv
    #
    cS
    cfv
    #
    @22
    cF
    cfv
    #
    cS
    cfv
    #
    @8
    cfv
    @20
    @0
    cfv
    #
    @22
    @0
    cfv
    #
    @8
    cfv
    @26
    cS
    cG
    cI
    @27
    @29
    @8
    wph
    @12
    @25
    dprdf1o.1
    adantr
    wph
    cS
    cdm
    cI
    wceq
    #
    @25
    dprdf1o.2
    adantr
    @26
    cJ
    cI
    @20
    cF
    wph
    @17
    @25
    @19
    adantr
    #
    wph
    @21
    @23
    @24
    simpr1
    #
    ffvelrnd
    @26
    cJ
    cI
    @22
    cF
    @34
    wph
    @21
    @23
    @24
    simpr2
    #
    ffvelrnd
    @26
    @27
    @29
    wne
    @24
    wph
    @21
    @23
    @24
    simpr3
    @26
    @27
    @29
    @20
    @22
    @26
    @13
    @21
    @23
    @27
    @29
    wceq
    @20
    @22
    wceq
    wb
    wph
    @13
    @25
    @15
    adantr
    @35
    @36
    cJ
    cI
    @20
    @22
    cF
    f1fveq
    syl12anc
    necon3bid
    mpbird
    @9
    dprdcntz
    @26
    @17
    @21
    @31
    @28
    wceq
    #
    @34
    @35
    cJ
    cI
    @20
    cS
    cF
    fvco3
    #
    syl2anc
    @26
    @32
    @30
    @8
    @26
    @17
    @23
    @32
    @30
    wceq
    @34
    @36
    cJ
    cI
    @22
    cS
    cF
    fvco3
    syl2anc
    fveq2d
    3sstr4d
    wph
    @21
    wa
    #
    @31
    @0
    cJ
    @20
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    @6
    cfv
    #
    cin
    #
    @7
    csn
    #
    wceq
    @45
    @46
    wss
    @39
    @45
    @28
    cS
    cI
    @27
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    @6
    cfv
    #
    cin
    @46
    @39
    @31
    @28
    @44
    @51
    wph
    @17
    @21
    @37
    @19
    @38
    sylan
    @39
    @43
    @50
    @6
    @39
    @42
    @49
    @39
    @42
    cS
    cF
    @41
    cima
    #
    cima
    @49
    cS
    cF
    @41
    imaco
    @39
    @52
    @48
    cS
    @39
    @52
    cF
    cJ
    cima
    #
    cF
    @40
    cima
    #
    cdif
    #
    @48
    @39
    @14
    cF
    ccnv
    wfun
    #
    @52
    @55
    wceq
    wph
    @14
    @21
    dprdf1o.3
    adantr
    #
    @14
    cJ
    cI
    cF
    wfo
    #
    @56
    cJ
    cI
    cF
    dff1o3
    simprbi
    cJ
    @40
    cF
    imadif
    3syl
    @39
    @53
    cI
    @54
    @47
    @39
    @14
    @58
    @53
    cI
    wceq
    @57
    cJ
    cI
    cF
    f1ofo
    #
    cJ
    cI
    cF
    foima
    3syl
    @39
    @47
    @54
    wph
    cF
    cJ
    wfn
    #
    @21
    @47
    @54
    wceq
    wph
    @14
    @60
    dprdf1o.3
    cJ
    cI
    cF
    f1ofn
    syl
    cJ
    @20
    cF
    fnsnfv
    sylan
    eqcomd
    difeq12d
    eqtrd
    imaeq2d
    syl5eq
    unieqd
    fveq2d
    ineq12d
    @39
    cS
    cG
    cI
    @6
    @27
    @7
    wph
    @12
    @21
    dprdf1o.1
    adantr
    wph
    @33
    @21
    dprdf1o.2
    adantr
    wph
    cJ
    cI
    @20
    cF
    @19
    ffvelrnda
    @10
    @11
    dprddisj
    eqtrd
    @45
    @46
    eqimss
    syl
    dmdprdd
    #
    wph
    @0
    crn
    #
    cuni
    #
    @6
    cfv
    #
    cS
    crn
    #
    cuni
    #
    @6
    cfv
    #
    @3
    @4
    wph
    @63
    @66
    @6
    wph
    @62
    @65
    wph
    @62
    cS
    cF
    crn
    #
    cima
    #
    @65
    cS
    cF
    rnco2
    wph
    @69
    cS
    cI
    cima
    #
    @65
    wph
    @68
    cI
    cS
    wph
    @14
    @58
    @68
    cI
    wceq
    dprdf1o.3
    @59
    cJ
    cI
    cF
    forn
    3syl
    imaeq2d
    wph
    @16
    cS
    cI
    wfn
    @70
    @65
    wceq
    @18
    cI
    @5
    cS
    ffn
    cI
    cS
    fnima
    3syl
    eqtrd
    syl5eq
    unieqd
    fveq2d
    wph
    @2
    @3
    @64
    wceq
    @61
    @0
    cG
    @6
    @11
    dprdspan
    syl
    wph
    @12
    @4
    @67
    wceq
    dprdf1o.1
    cS
    cG
    @6
    @11
    dprdspan
    syl
    3eqtr4d
    jca
end
