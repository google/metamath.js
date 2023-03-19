include "wcel.mm"
include "crefld.mm"
include "cfrlm.mm"
include "co.mm"
include "ctch.mm"
include "cfv.mm"
include "ccph.mm"
include "rrxval.mm"
include "csca.mm"
include "cip.mm"
include "cr.mm"
include "cbs.mm"
include "eqid.mm"
include "cmul.mm"
include "ccj.mm"
include "c0g.mm"
include "cc0.mm"
include "rebase.mm"
include "remulr.mm"
include "re0g.mm"
include "refldcj.mm"
include "cfield.mm"
include "refld.mm"
include "a1i.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "wfn.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "frlmbasf.mm"
include "ffn.mm"
include "syl.mm"
include "3adant3.mm"
include "cof.mm"
include "csupp.mm"
include "cdif.mm"
include "wo.mm"
include "csu.mm"
include "cgsu.mm"
include "simpl.mm"
include "simpr.mm"
include "frlmipval.mm"
include "syl22anc.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cvv.mm"
include "ovexd.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "ofval.mm"
include "ffvelrnda.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "fmpt2d.mm"
include "wfun.mm"
include "wss.mm"
include "ffun.mm"
include "frlmbasfsupp.mm"
include "0red.mm"
include "recnd.mm"
include "mul02d.mm"
include "suppofss1d.mm"
include "fsuppsssupp.mm"
include "regsumsupp.mm"
include "syl3anc.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "sselda.mm"
include "syldan.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "simp3.mm"
include "eqtr3d.mm"
include "wb.mm"
include "cfn.mm"
include "fsuppimpd.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cle.mm"
include "msqge0d.mm"
include "fsum00.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "3adantl3.mm"
include "mul0ord.mm"
include "adantr.mm"
include "oridm.mm"
include "sylib.mm"
include "ssid.mm"
include "simpl1.mm"
include "suppssr.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "cun.mm"
include "undif.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "elun.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "fconstfv.mm"
include "c0ex.mm"
include "fconst2.mm"
include "sylbb1.mm"
include "crg.mm"
include "cdr.mm"
include "ccrg.mm"
include "isfld.mm"
include "mpbi.mm"
include "simpli.mm"
include "drngring.mm"
include "ax-mp.mm"
include "frlm0.mm"
include "mpan.mm"
include "syl5reqr.mm"
include "3ad2ant1.mm"
include "3eqtr4a.mm"
include "cjre.mm"
include "adantl.mm"
include "id.mm"
include "frlmphl.mm"
include "ccnfld.mm"
include "cress.mm"
include "df-refld.mm"
include "frlmsca.mm"
include "simpr1.mm"
include "simpr3.mm"
include "resqrtcld.mm"
include "fsumge0.mm"
include "breqtrrd.mm"
include "tchcph.mm"

theorem rrxcph
  let cB: class B
  let cH: class H
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )
  assume rrxbase.b: |- B = ( Base ` H )


  assert |- ( I e. V -> H e. CPreHil )

  proof
    cI
    cV
    wcel
    #
    cH
    crefld
    cI
    cfrlm
    co
    #
    ctch
    cfv
    #
    ccph
    cH
    cI
    cV
    rrxval.r
    rrxval
    @0
    vf
    @1
    csca
    cfv
    #
    @2
    @1
    cip
    cfv
    #
    cr
    @1
    cbs
    cfv
    #
    @1
    @2
    eqid
    @5
    eqid
    #
    @3
    eqid
    @0
    vx
    cr
    crefld
    cmul
    vf
    @4
    cI
    ccj
    @1
    c0g
    cfv
    #
    @5
    cV
    @1
    cc0
    @1
    eqid
    #
    rebase
    remulr
    @6
    @4
    eqid
    #
    @7
    eqid
    re0g
    refldcj
    crefld
    cfield
    wcel
    #
    @0
    refld
    a1i
    @0
    vf
    cv
    #
    @5
    wcel
    #
    @11
    @11
    @4
    co
    #
    cc0
    wceq
    #
    w3a
    #
    cI
    cc0
    csn
    #
    cxp
    #
    vx
    cI
    cc0
    cmpt
    #
    @11
    @7
    vx
    cI
    cc0
    fconstmpt
    #
    @15
    @11
    cI
    wfn
    #
    vx
    cv
    #
    @11
    cfv
    #
    cc0
    wceq
    #
    vx
    cI
    wral
    #
    @11
    @17
    wceq
    #
    @0
    @12
    @20
    @14
    @0
    @12
    wa
    #
    cI
    cr
    @11
    wf
    #
    @20
    @5
    crefld
    @1
    cI
    cr
    cV
    @11
    @8
    rebase
    @6
    frlmbasf
    #
    cI
    cr
    @11
    ffn
    syl
    #
    3adant3
    @15
    @23
    vx
    cI
    @15
    @21
    cI
    wcel
    #
    wa
    #
    @21
    @11
    @11
    cmul
    cof
    #
    co
    #
    cc0
    csupp
    co
    #
    wcel
    #
    @23
    @21
    cI
    @34
    cdif
    #
    wcel
    #
    @31
    @35
    wa
    #
    @23
    @23
    wo
    #
    @23
    @38
    @22
    @22
    cmul
    co
    #
    cc0
    wceq
    #
    @39
    @15
    @35
    @41
    @30
    @15
    @41
    vx
    @34
    @15
    @34
    @40
    vx
    csu
    #
    cc0
    wceq
    #
    @41
    vx
    @34
    wral
    #
    @15
    @13
    @42
    cc0
    @0
    @12
    @13
    @42
    wceq
    @14
    @26
    @13
    crefld
    @33
    cgsu
    co
    #
    @42
    @26
    @0
    @10
    @12
    @12
    @13
    @45
    wceq
    @0
    @12
    simpl
    #
    @10
    @26
    refld
    a1i
    @0
    @12
    simpr
    #
    @47
    cr
    crefld
    cmul
    @11
    @11
    @4
    cI
    @5
    cV
    cfield
    @1
    @8
    rebase
    remulr
    @6
    @9
    frlmipval
    syl22anc
    #
    @26
    @45
    @34
    @21
    @33
    cfv
    #
    vx
    csu
    #
    @42
    @26
    cI
    cr
    @33
    wf
    #
    @33
    cc0
    cfsupp
    wbr
    #
    @0
    @45
    @50
    wceq
    @26
    vx
    vx
    cI
    @40
    cr
    @33
    cvv
    @26
    @30
    wa
    #
    @22
    @22
    cmul
    ovexd
    @26
    vx
    cI
    cI
    @22
    @22
    cmul
    cI
    @11
    @11
    cV
    cV
    @29
    @29
    @46
    @46
    cI
    inidm
    #
    @53
    @22
    eqidd
    #
    @55
    offval
    @53
    @49
    @40
    cr
    @26
    cI
    cI
    @22
    @22
    cmul
    cI
    @11
    @11
    cV
    cV
    @21
    @29
    @29
    @46
    @46
    @54
    @55
    @55
    ofval
    #
    @53
    @22
    @22
    @26
    cI
    cr
    @21
    @11
    @28
    ffvelrnda
    #
    @57
    remulcld
    #
    eqeltrd
    fmpt2d
    #
    @26
    @33
    cvv
    wcel
    @33
    wfun
    #
    @11
    cc0
    cfsupp
    wbr
    @34
    @11
    cc0
    csupp
    co
    #
    wss
    #
    @52
    @26
    @11
    @11
    @32
    ovexd
    @26
    @51
    @60
    @59
    cI
    cr
    @33
    ffun
    syl
    @5
    crefld
    @1
    cI
    cV
    @11
    cc0
    @8
    re0g
    @6
    frlmbasfsupp
    #
    @26
    vx
    cI
    cr
    @11
    @11
    cV
    cmul
    cc0
    @46
    @26
    0red
    @28
    @28
    @26
    @21
    cr
    wcel
    #
    wa
    #
    @21
    @65
    @21
    @26
    @64
    simpr
    recnd
    mul02d
    suppofss1d
    #
    @11
    @33
    cvv
    cc0
    fsuppsssupp
    syl22anc
    @46
    vx
    @33
    cI
    cV
    regsumsupp
    syl3anc
    @26
    @34
    @49
    @40
    vx
    @26
    @35
    @30
    @49
    @40
    wceq
    #
    @26
    @34
    cI
    @21
    @26
    @34
    @61
    cI
    @66
    @26
    @11
    cdm
    #
    @61
    cI
    @11
    cc0
    suppssdm
    @26
    @27
    @68
    cI
    wceq
    @28
    cI
    cr
    @11
    fdm
    syl
    syl5sseq
    sstrd
    #
    sselda
    #
    @56
    syldan
    sumeq2dv
    eqtrd
    #
    eqtrd
    3adant3
    @0
    @12
    @14
    simp3
    eqtr3d
    @0
    @12
    @43
    @44
    wb
    @14
    @26
    @34
    @40
    vx
    @26
    @61
    cfn
    wcel
    @62
    @34
    cfn
    wcel
    @26
    @11
    cc0
    @63
    fsuppimpd
    @66
    @61
    @34
    ssfi
    syl2anc
    #
    @26
    @35
    @30
    @40
    cr
    wcel
    @70
    @58
    syldan
    #
    @26
    @35
    @30
    cc0
    @40
    cle
    wbr
    @70
    @53
    @22
    @57
    msqge0d
    syldan
    #
    fsum00
    3adant3
    mpbid
    r19.21bi
    adantlr
    @31
    @41
    @39
    wb
    @35
    @31
    @22
    @22
    @31
    @22
    @0
    @12
    @30
    @22
    cr
    wcel
    @14
    @57
    3adantl3
    recnd
    #
    @75
    mul0ord
    #
    adantr
    mpbid
    @23
    oridm
    #
    sylib
    @31
    @37
    @49
    cc0
    wceq
    #
    @23
    @31
    cI
    cr
    cr
    @33
    cV
    @34
    @21
    cc0
    @15
    @51
    @30
    @0
    @12
    @51
    @14
    @59
    3adant3
    adantr
    @34
    @34
    wss
    @31
    @34
    ssid
    a1i
    @0
    @12
    @14
    @30
    simpl1
    @31
    0red
    suppssr
    @31
    @78
    @23
    @31
    @78
    @39
    @23
    @31
    @78
    @41
    @39
    @31
    @49
    @40
    cc0
    @0
    @12
    @30
    @67
    @14
    @56
    3adantl3
    eqeq1d
    @76
    bitrd
    @77
    syl6bb
    biimpa
    syldan
    @31
    @21
    @34
    @36
    cun
    #
    wcel
    #
    @35
    @37
    wo
    @15
    @80
    @30
    @0
    @12
    @80
    @30
    wb
    @14
    @26
    @79
    cI
    @21
    @26
    @34
    cI
    wss
    @79
    cI
    wceq
    @69
    @34
    cI
    undif
    sylib
    eleq2d
    3adant3
    biimpar
    @21
    @34
    @36
    elun
    sylib
    mpjaodan
    ralrimiva
    cI
    @16
    @11
    wf
    @20
    @24
    wa
    @25
    vx
    cI
    cc0
    @11
    fconstfv
    cI
    cc0
    @11
    c0ex
    fconst2
    sylbb1
    syl2anc
    @0
    @12
    @7
    @18
    wceq
    @14
    @0
    @18
    @17
    @7
    @19
    crefld
    crg
    wcel
    #
    @0
    @17
    @7
    wceq
    crefld
    cdr
    wcel
    #
    @81
    @82
    crefld
    ccrg
    wcel
    #
    @10
    @82
    @83
    wa
    refld
    crefld
    isfld
    mpbi
    simpli
    crefld
    drngring
    ax-mp
    crefld
    @1
    cI
    cV
    cc0
    @8
    re0g
    frlm0
    mpan
    syl5reqr
    3ad2ant1
    3eqtr4a
    @64
    @21
    ccj
    cfv
    @21
    wceq
    @0
    @21
    cjre
    adantl
    @0
    id
    frlmphl
    @0
    ccnfld
    cr
    cress
    co
    crefld
    @3
    df-refld
    @10
    @0
    crefld
    @3
    wceq
    refld
    crefld
    @1
    cI
    cfield
    cV
    @8
    frlmsca
    mpan
    syl5reqr
    @9
    @0
    @11
    cr
    wcel
    #
    @84
    cc0
    @11
    cle
    wbr
    #
    w3a
    wa
    @11
    @0
    @84
    @84
    @85
    simpr1
    @0
    @84
    @84
    @85
    simpr3
    resqrtcld
    @26
    cc0
    @45
    @13
    cle
    @26
    cc0
    @42
    @45
    cle
    @26
    @34
    @40
    vx
    @72
    @73
    @74
    fsumge0
    @71
    breqtrrd
    @48
    breqtrrd
    tchcph
    eqeltrd
end
