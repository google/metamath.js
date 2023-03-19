include "cr.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "wf.mm"
include "i1ff.mm"
include "syl.mm"
include "adantr.mm"
include "0red.mm"
include "cv.mm"
include "simplr.mm"
include "oveq1d.mm"
include "mul02lem2.mm"
include "adantl.mm"
include "eqtrd.mm"
include "caofid2.mm"
include "i1f0.mm"
include "syl6eqel.mm"
include "wne.mm"
include "remulcl.mm"
include "fconst6g.mm"
include "inidm.mm"
include "off.mm"
include "crn.mm"
include "cfn.mm"
include "cmpt.mm"
include "wss.mm"
include "wfo.mm"
include "i1frn.mm"
include "wfn.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fofi.mm"
include "sylancl.mm"
include "wrex.mm"
include "cab.mm"
include "id.mm"
include "elsni.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anr.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "fconstg.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "frn.mm"
include "rnmpt.mm"
include "syl6sseqr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cdiv.mm"
include "cvol.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "i1fmulclem.mm"
include "syldan.mm"
include "i1fima.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "cfv.mm"
include "fveq2d.mm"
include "redivcld.mm"
include "recnd.mm"
include "eldifsni.mm"
include "divne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "i1fima2sn.mm"
include "i1fd.mm"
include "pm2.61dane.mm"

theorem i1fmulc
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume i1fmulc.2: |- ( ph -> F e. dom S.1 )
  assume i1fmulc.3: |- ( ph -> A e. RR )


  assert |- ( ph -> ( ( RR X. { A } ) oF x. F ) e. dom S.1 )

  proof
    wph
    cr
    cA
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    co
    #
    citg1
    cdm
    #
    wcel
    cA
    cc0
    wph
    cA
    cc0
    wceq
    #
    wa
    #
    @2
    cr
    cc0
    csn
    #
    cxp
    @3
    @5
    vx
    cr
    cA
    cc0
    cmul
    cr
    cF
    cvv
    cr
    cr
    cr
    cvv
    wcel
    #
    @5
    reex
    a1i
    wph
    cr
    cr
    cF
    wf
    #
    @4
    wph
    cF
    @3
    wcel
    #
    @8
    i1fmulc.2
    cF
    i1ff
    syl
    #
    adantr
    wph
    cA
    cr
    wcel
    #
    @4
    i1fmulc.3
    adantr
    @5
    0red
    @5
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    cA
    @12
    cmul
    co
    cc0
    @12
    cmul
    co
    #
    cc0
    @14
    cA
    cc0
    @12
    cmul
    wph
    @4
    @13
    simplr
    oveq1d
    @13
    @15
    cc0
    wceq
    @5
    @12
    mul02lem2
    adantl
    eqtrd
    caofid2
    i1f0
    syl6eqel
    wph
    cA
    cc0
    wne
    #
    wa
    #
    vy
    @2
    wph
    cr
    cr
    @2
    wf
    #
    @16
    wph
    vx
    vy
    cr
    cr
    cr
    cmul
    cr
    cr
    cr
    @1
    cF
    cvv
    cvv
    @13
    vy
    cv
    #
    cr
    wcel
    #
    wa
    @12
    @19
    cmul
    co
    cr
    wcel
    wph
    @12
    @19
    remulcl
    adantl
    wph
    @11
    cr
    cr
    @1
    wf
    i1fmulc.3
    cr
    cA
    cr
    fconst6g
    syl
    @10
    @7
    wph
    reex
    a1i
    #
    @21
    cr
    inidm
    #
    off
    #
    adantr
    wph
    @2
    crn
    #
    cfn
    wcel
    #
    @16
    wph
    vy
    cF
    crn
    #
    cA
    @19
    cmul
    co
    #
    cmpt
    #
    crn
    #
    cfn
    wcel
    #
    @24
    @29
    wss
    @25
    wph
    @26
    cfn
    wcel
    #
    @26
    @29
    @28
    wfo
    #
    @30
    wph
    @9
    @31
    i1fmulc.2
    cF
    i1frn
    syl
    @28
    @26
    wfn
    @32
    vy
    @26
    @27
    @28
    cA
    @19
    cmul
    ovex
    @28
    eqid
    #
    fnmpti
    @26
    @28
    dffn4
    mpbi
    @26
    @29
    @28
    fofi
    sylancl
    wph
    @24
    vz
    cv
    #
    @27
    wceq
    #
    vy
    @26
    wrex
    #
    vz
    cab
    #
    @29
    wph
    cr
    @37
    @2
    wf
    @24
    @37
    wss
    wph
    vx
    vw
    cr
    cr
    cr
    cmul
    @0
    @26
    @37
    @1
    cF
    cvv
    cvv
    @12
    @0
    wcel
    #
    vw
    cv
    #
    @26
    wcel
    #
    wa
    #
    @12
    @39
    cmul
    co
    #
    @37
    wcel
    #
    wph
    @41
    @42
    @27
    wceq
    #
    vy
    @26
    wrex
    #
    @43
    @40
    @40
    @42
    cA
    @39
    cmul
    co
    #
    wceq
    #
    @45
    @38
    @40
    id
    @38
    @12
    cA
    @39
    cmul
    @12
    cA
    elsni
    oveq1d
    @44
    @47
    vy
    @39
    @26
    @19
    @39
    wceq
    @27
    @46
    @42
    @19
    @39
    cA
    cmul
    oveq2
    eqeq2d
    rspcev
    syl2anr
    @36
    @45
    vz
    @42
    @12
    @39
    cmul
    ovex
    @34
    @42
    wceq
    @35
    @44
    vy
    @26
    @34
    @42
    @27
    eqeq1
    rexbidv
    elab
    sylibr
    adantl
    wph
    @11
    cr
    @0
    @1
    wf
    i1fmulc.3
    cr
    cA
    cr
    fconstg
    syl
    wph
    cF
    cr
    wfn
    #
    cr
    @26
    cF
    wf
    wph
    @8
    @48
    @10
    cr
    cr
    cF
    ffn
    syl
    cr
    cF
    dffn3
    sylib
    @21
    @21
    @22
    off
    cr
    @37
    @2
    frn
    syl
    vy
    vz
    @26
    @27
    @28
    @33
    rnmpt
    syl6sseqr
    @29
    @24
    ssfi
    syl2anc
    adantr
    @17
    @19
    @24
    @6
    cdif
    #
    wcel
    #
    wa
    #
    @2
    ccnv
    @19
    csn
    cima
    #
    cF
    ccnv
    @19
    cA
    cdiv
    co
    #
    csn
    #
    cima
    #
    cvol
    cdm
    #
    @17
    @50
    @20
    @52
    @55
    wceq
    @17
    @49
    cr
    @19
    wph
    @49
    cr
    wss
    @16
    wph
    @24
    cr
    @6
    wph
    @18
    @24
    cr
    wss
    @23
    cr
    cr
    @2
    frn
    syl
    ssdifssd
    adantr
    sselda
    #
    wph
    cA
    @19
    cF
    i1fmulc.2
    i1fmulc.3
    i1fmulclem
    syldan
    #
    wph
    @55
    @56
    wcel
    #
    @16
    @50
    wph
    @9
    @59
    i1fmulc.2
    @54
    cF
    i1fima
    syl
    ad2antrr
    eqeltrd
    @51
    @52
    cvol
    cfv
    @55
    cvol
    cfv
    #
    cr
    @51
    @52
    @55
    cvol
    @58
    fveq2d
    @51
    @9
    @53
    cr
    @6
    cdif
    wcel
    #
    @60
    cr
    wcel
    wph
    @9
    @16
    @50
    i1fmulc.2
    ad2antrr
    @51
    @53
    cr
    wcel
    @53
    cc0
    wne
    @61
    @51
    @19
    cA
    @57
    wph
    @11
    @16
    @50
    i1fmulc.3
    ad2antrr
    #
    wph
    @16
    @50
    simplr
    #
    redivcld
    @51
    @19
    cA
    @51
    @19
    @57
    recnd
    @51
    cA
    @62
    recnd
    @50
    @19
    cc0
    wne
    @17
    @19
    @24
    cc0
    eldifsni
    adantl
    @63
    divne0d
    @53
    cr
    cc0
    eldifsn
    sylanbrc
    @53
    cr
    cF
    i1fima2sn
    syl2anc
    eqeltrd
    i1fd
    pm2.61dane
end
