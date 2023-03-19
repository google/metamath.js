include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "crn.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "reldmdprd.mm"
include "brrelex2i.mm"
include "a1i.mm"
include "adantr.mm"
include "wb.mm"
include "wf.mm"
include "cv.mm"
include "ccntz.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "cmrc.mm"
include "cin.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "ffvelrn.mm"
include "ad2ant2lr.mm"
include "eqid.mm"
include "subgss.mm"
include "syl.mm"
include "subgbas.mm"
include "ad2antrr.mm"
include "sseqtr4d.mm"
include "biantrud.mm"
include "simpll.mm"
include "simplr.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "ffvelrnd.mm"
include "resscntz.mm"
include "syl2anc.mm"
include "sseq2d.mm"
include "ssin.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "subgrcl.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "subggrp.mm"
include "imassrn.mm"
include "frn.mm"
include "ad2antlr.mm"
include "syl5ss.mm"
include "mresspw.mm"
include "sstrd.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrcssidd.mm"
include "mrccl.mm"
include "subsubg.mm"
include "mpbid.mm"
include "simpld.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "eqssd.mm"
include "ineq2d.mm"
include "subg0.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "pm5.32da.mm"
include "wfn.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "eqrdv.mm"
include "anbi2d.mm"
include "df-f.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitr4g.mm"
include "anbi1d.mm"
include "bitr3d.mm"
include "dmexg.mm"
include "adantl.mm"
include "eqidd.mm"
include "w3a.mm"
include "dmdprd.mm"
include "3anass.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl21anc.mm"
include "an32.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem subgdmdprd
  let cA: class A
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgdprd.1: |- H = ( G |`s A )


  assert |- ( A e. ( SubGrp ` G ) -> ( H dom DProd S <-> ( G dom DProd S /\ ran S C_ ~P A ) ) )

  proof
    cA
    cG
    csubg
    cfv
    #
    wcel
    #
    cS
    cvv
    wcel
    #
    cH
    cS
    cdprd
    cdm
    #
    wbr
    #
    cG
    cS
    @3
    wbr
    #
    cS
    crn
    #
    cA
    cpw
    #
    wss
    #
    wa
    #
    @4
    @2
    wi
    @1
    cH
    cS
    @3
    reldmdprd
    brrelex2i
    a1i
    @9
    @2
    wi
    @1
    @5
    @2
    @8
    cG
    cS
    @3
    reldmdprd
    brrelex2i
    adantr
    a1i
    @1
    @2
    @4
    @9
    wb
    @1
    @2
    wa
    #
    cS
    cdm
    #
    cH
    csubg
    cfv
    #
    cS
    wf
    #
    vx
    cv
    #
    cS
    cfv
    #
    vy
    cv
    #
    cS
    cfv
    #
    cH
    ccntz
    cfv
    #
    cfv
    #
    wss
    #
    vy
    @11
    @14
    csn
    #
    cdif
    #
    wral
    #
    @15
    cS
    @22
    cima
    #
    cuni
    #
    @12
    cmrc
    cfv
    #
    cfv
    #
    cin
    #
    cH
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wa
    #
    vx
    @11
    wral
    #
    wa
    #
    @11
    @0
    cS
    wf
    #
    @8
    wa
    #
    @15
    @17
    cG
    ccntz
    cfv
    #
    cfv
    #
    wss
    #
    vy
    @22
    wral
    #
    @15
    @25
    @0
    cmrc
    cfv
    #
    cfv
    #
    cin
    #
    cG
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wa
    #
    vx
    @11
    wral
    #
    wa
    #
    @4
    @9
    @1
    @34
    @49
    wb
    @2
    @1
    @13
    @48
    wa
    @34
    @49
    @1
    @13
    @48
    @33
    @1
    @13
    wa
    #
    @47
    @32
    vx
    @11
    @50
    @14
    @11
    wcel
    #
    wa
    #
    @40
    @23
    @46
    @31
    @52
    @39
    @20
    vy
    @22
    @50
    @51
    @16
    @22
    wcel
    #
    @39
    @20
    wb
    @50
    @51
    @53
    wa
    #
    wa
    #
    @39
    @39
    @15
    cA
    wss
    #
    wa
    #
    @20
    @55
    @56
    @39
    @55
    @15
    cH
    cbs
    cfv
    #
    cA
    @55
    @15
    @12
    wcel
    #
    @15
    @58
    wss
    @13
    @51
    @59
    @1
    @53
    @11
    @12
    @14
    cS
    ffvelrn
    ad2ant2lr
    @58
    @15
    cH
    @58
    eqid
    #
    subgss
    syl
    @1
    cA
    @58
    wceq
    #
    @13
    @54
    cA
    cG
    cH
    subgdprd.1
    subgbas
    #
    ad2antrr
    #
    sseqtr4d
    biantrud
    @55
    @20
    @15
    @38
    cA
    cin
    #
    wss
    @57
    @55
    @19
    @64
    @15
    @55
    @1
    @17
    cA
    wss
    @19
    @64
    wceq
    @1
    @13
    @54
    simpll
    @55
    @17
    @58
    cA
    @55
    @17
    @12
    wcel
    @17
    @58
    wss
    @55
    @11
    @12
    @16
    cS
    @1
    @13
    @54
    simplr
    @53
    @16
    @11
    wcel
    @50
    @51
    @16
    @11
    @21
    eldifi
    ad2antll
    ffvelrnd
    @58
    @17
    cH
    @60
    subgss
    syl
    @63
    sseqtr4d
    cA
    @17
    cG
    cH
    @0
    @18
    @37
    subgdprd.1
    @37
    eqid
    #
    @18
    eqid
    #
    resscntz
    syl2anc
    sseq2d
    @15
    @38
    cA
    ssin
    syl6bbr
    bitr4d
    anassrs
    ralbidva
    @52
    @43
    @28
    @45
    @30
    @52
    @42
    @27
    @15
    @52
    @42
    @27
    @52
    @0
    cG
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    @25
    @27
    wss
    @27
    @0
    wcel
    #
    @42
    @27
    wss
    @52
    cG
    cgrp
    wcel
    #
    @0
    @67
    cacs
    cfv
    wcel
    @68
    @1
    @70
    @13
    @51
    cA
    cG
    subgrcl
    #
    ad2antrr
    @67
    cG
    @67
    eqid
    #
    subgacs
    @0
    @67
    acsmre
    3syl
    #
    @52
    @12
    @25
    @26
    @58
    @52
    cH
    cgrp
    wcel
    #
    @12
    @58
    cacs
    cfv
    wcel
    @12
    @58
    cmre
    cfv
    wcel
    #
    @1
    @74
    @13
    @51
    cA
    cG
    cH
    subgdprd.1
    subggrp
    #
    ad2antrr
    @58
    cH
    @60
    subgacs
    @12
    @58
    acsmre
    3syl
    #
    @26
    eqid
    #
    @52
    @24
    @58
    cpw
    #
    wss
    @25
    @58
    wss
    #
    @52
    @24
    @12
    @79
    @52
    @24
    @6
    @12
    cS
    @22
    imassrn
    @13
    @6
    @12
    wss
    #
    @1
    @51
    @11
    @12
    cS
    frn
    ad2antlr
    syl5ss
    @52
    @75
    @12
    @79
    wss
    @77
    @12
    @58
    mresspw
    syl
    sstrd
    @24
    @58
    sspwuni
    sylib
    #
    mrcssidd
    @52
    @69
    @27
    cA
    wss
    #
    @52
    @27
    @12
    wcel
    #
    @69
    @83
    wa
    #
    @52
    @75
    @80
    @84
    @77
    @82
    @12
    @25
    @26
    @58
    @78
    mrccl
    syl2anc
    @1
    @84
    @85
    wb
    @13
    @51
    @27
    cA
    cG
    cH
    subgdprd.1
    subsubg
    ad2antrr
    mpbid
    simpld
    @0
    @25
    @41
    @27
    @67
    @41
    eqid
    #
    mrcsscl
    syl3anc
    @52
    @75
    @25
    @42
    wss
    @42
    @12
    wcel
    #
    @27
    @42
    wss
    @77
    @52
    @0
    @25
    @41
    @67
    @73
    @86
    @52
    @25
    cA
    @67
    @52
    @25
    @58
    cA
    @82
    @1
    @61
    @13
    @51
    @62
    ad2antrr
    sseqtr4d
    #
    @1
    cA
    @67
    wss
    @13
    @51
    @67
    cA
    cG
    @72
    subgss
    ad2antrr
    sstrd
    #
    mrcssidd
    @52
    @87
    @42
    @0
    wcel
    #
    @42
    cA
    wss
    #
    @52
    @68
    @25
    @67
    wss
    @90
    @73
    @89
    @0
    @25
    @41
    @67
    @86
    mrccl
    syl2anc
    @52
    @68
    @25
    cA
    wss
    @1
    @91
    @73
    @88
    @1
    @13
    @51
    simpll
    @0
    @25
    @41
    cA
    @67
    @86
    mrcsscl
    syl3anc
    @1
    @87
    @90
    @91
    wa
    wb
    @13
    @51
    @42
    cA
    cG
    cH
    subgdprd.1
    subsubg
    ad2antrr
    mpbir2and
    @12
    @25
    @26
    @42
    @58
    @78
    mrcsscl
    syl3anc
    eqssd
    ineq2d
    @52
    @44
    @29
    @1
    @44
    @29
    wceq
    @13
    @51
    cA
    cG
    cH
    @44
    subgdprd.1
    @44
    eqid
    #
    subg0
    ad2antrr
    sneqd
    eqeq12d
    anbi12d
    ralbidva
    pm5.32da
    @1
    @13
    @36
    @48
    @1
    cS
    @11
    wfn
    #
    @81
    wa
    @93
    @6
    @0
    wss
    #
    @8
    wa
    #
    wa
    #
    @13
    @36
    @1
    @81
    @95
    @93
    @1
    @81
    @6
    @0
    @7
    cin
    #
    wss
    @95
    @1
    @12
    @97
    @6
    @1
    vx
    @12
    @97
    @1
    @14
    @12
    wcel
    @14
    @0
    wcel
    #
    @14
    cA
    wss
    #
    wa
    #
    @14
    @97
    wcel
    #
    @14
    cA
    cG
    cH
    subgdprd.1
    subsubg
    @101
    @98
    @14
    @7
    wcel
    #
    wa
    @100
    @14
    @0
    @7
    elin
    @102
    @99
    @98
    vx
    cA
    selpw
    anbi2i
    bitri
    syl6bbr
    eqrdv
    sseq2d
    @6
    @0
    @7
    ssin
    syl6bbr
    anbi2d
    @11
    @12
    cS
    df-f
    @36
    @93
    @94
    wa
    #
    @8
    wa
    @96
    @35
    @103
    @8
    @11
    @0
    cS
    df-f
    anbi1i
    @93
    @94
    @8
    anass
    bitri
    3bitr4g
    anbi1d
    bitr3d
    adantr
    @10
    @11
    cvv
    wcel
    #
    @11
    @11
    wceq
    #
    @74
    @4
    @34
    wb
    @2
    @104
    @1
    cS
    cvv
    dmexg
    adantl
    #
    @10
    @11
    eqidd
    #
    @1
    @74
    @2
    @76
    adantr
    @104
    @105
    wa
    #
    @4
    @74
    @34
    @108
    @4
    @74
    @13
    @33
    w3a
    @74
    @34
    wa
    vx
    vy
    cS
    cH
    @11
    @26
    cvv
    @29
    @18
    @66
    @29
    eqid
    @78
    dmdprd
    @74
    @13
    @33
    3anass
    syl6bb
    baibd
    syl21anc
    @10
    @9
    @35
    @48
    wa
    #
    @8
    wa
    @49
    @10
    @5
    @109
    @8
    @10
    @104
    @105
    @70
    @5
    @109
    wb
    @106
    @107
    @1
    @70
    @2
    @71
    adantr
    @108
    @5
    @70
    @109
    @108
    @5
    @70
    @35
    @48
    w3a
    @70
    @109
    wa
    vx
    vy
    cS
    cG
    @11
    @41
    cvv
    @44
    @37
    @65
    @92
    @86
    dmdprd
    @70
    @35
    @48
    3anass
    syl6bb
    baibd
    syl21anc
    anbi1d
    @35
    @48
    @8
    an32
    syl6bb
    3bitr4d
    ex
    pm5.21ndd
end
