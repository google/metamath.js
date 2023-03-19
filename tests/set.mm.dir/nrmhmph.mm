include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cnrm.mm"
include "wcel.mm"
include "wi.mm"
include "hmph.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "ctop.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "wrex.mm"
include "ccld.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "ccn.mm"
include "hmeocn.mm"
include "adantl.mm"
include "cntop2.mm"
include "syl.mm"
include "ccnv.mm"
include "cima.mm"
include "simpll.mm"
include "adantr.mm"
include "simprl.mm"
include "cnima.mm"
include "syl2anc.mm"
include "inss1.mm"
include "simprr.mm"
include "sseldi.mm"
include "cnclima.mm"
include "inss2.mm"
include "elpwid.mm"
include "imass2.mm"
include "nrmsep3.mm"
include "syl13anc.mm"
include "simpllr.mm"
include "hmeoima.mm"
include "simprrl.mm"
include "wfun.mm"
include "crn.mm"
include "cuni.mm"
include "wf1o.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "f1ofun.mm"
include "cldss.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "sseqtr4d.mm"
include "funimass1.mm"
include "mpd.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "hmeocls.mm"
include "simprrr.mm"
include "cdm.mm"
include "wb.mm"
include "nrmtop.mm"
include "ad3antrrr.mm"
include "clsss3.mm"
include "f1odm.mm"
include "funimass3.mm"
include "mpbird.mm"
include "eqsstrd.mm"
include "sseq2.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "isnrm.mm"
include "sylanbrc.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem nrmhmph
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J ~= K -> ( J e. Nrm -> K e. Nrm ) )

  proof
    cJ
    cK
    chmph
    wbr
    cJ
    cK
    chmeo
    co
    #
    c0
    wne
    #
    cJ
    cnrm
    wcel
    #
    cK
    cnrm
    wcel
    #
    wi
    #
    cJ
    cK
    hmph
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @4
    vf
    @0
    n0
    @6
    @4
    vf
    @2
    @6
    @3
    @2
    @6
    wa
    #
    cK
    ctop
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    @10
    cK
    ccl
    cfv
    #
    cfv
    #
    vx
    cv
    #
    wss
    #
    wa
    #
    vz
    cK
    wrex
    #
    vy
    cK
    ccld
    cfv
    #
    @14
    cpw
    #
    cin
    #
    wral
    vx
    cK
    wral
    @3
    @7
    @5
    cJ
    cK
    ccn
    co
    wcel
    #
    @8
    @6
    @21
    @2
    @5
    cJ
    cK
    hmeocn
    adantl
    #
    @5
    cJ
    cK
    cntop2
    syl
    @7
    @17
    vx
    vy
    cK
    @20
    @7
    @14
    cK
    wcel
    #
    @9
    @20
    wcel
    #
    wa
    #
    wa
    #
    @5
    ccnv
    #
    @9
    cima
    #
    vw
    cv
    #
    wss
    #
    @29
    cJ
    ccl
    cfv
    cfv
    #
    @27
    @14
    cima
    #
    wss
    #
    wa
    #
    @17
    vw
    cJ
    @26
    @2
    @32
    cJ
    wcel
    #
    @28
    cJ
    ccld
    cfv
    wcel
    #
    @28
    @32
    wss
    #
    @34
    vw
    cJ
    wrex
    @2
    @6
    @25
    simpll
    @26
    @21
    @23
    @35
    @7
    @21
    @25
    @22
    adantr
    #
    @7
    @23
    @24
    simprl
    @14
    @5
    cJ
    cK
    cnima
    syl2anc
    @26
    @21
    @9
    @18
    wcel
    #
    @36
    @38
    @26
    @20
    @18
    @9
    @18
    @19
    inss1
    @7
    @23
    @24
    simprr
    #
    sseldi
    #
    @9
    @5
    cJ
    cK
    cnclima
    syl2anc
    @26
    @9
    @14
    wss
    @37
    @26
    @9
    @14
    @26
    @20
    @19
    @9
    @18
    @19
    inss2
    @40
    sseldi
    elpwid
    @9
    @14
    @27
    imass2
    syl
    vw
    @32
    @28
    cJ
    nrmsep3
    syl13anc
    @26
    @29
    cJ
    wcel
    #
    @34
    wa
    #
    wa
    #
    @5
    @29
    cima
    #
    cK
    wcel
    #
    @9
    @45
    wss
    #
    @45
    @12
    cfv
    #
    @14
    wss
    #
    @17
    @44
    @6
    @42
    @46
    @2
    @6
    @25
    @43
    simpllr
    #
    @26
    @42
    @34
    simprl
    @29
    @5
    cJ
    cK
    hmeoima
    syl2anc
    @44
    @30
    @47
    @26
    @42
    @30
    @33
    simprrl
    @44
    @5
    wfun
    #
    @9
    @5
    crn
    #
    wss
    @30
    @47
    wi
    @44
    cJ
    cuni
    #
    cK
    cuni
    #
    @5
    wf1o
    #
    @51
    @44
    @6
    @55
    @50
    @5
    cJ
    cK
    @53
    @54
    @53
    eqid
    #
    @54
    eqid
    #
    hmeof1o
    syl
    #
    @53
    @54
    @5
    f1ofun
    syl
    #
    @44
    @9
    @54
    @52
    @44
    @39
    @9
    @54
    wss
    @26
    @39
    @43
    @41
    adantr
    @9
    cK
    @54
    @57
    cldss
    syl
    @44
    @55
    @53
    @54
    @5
    wfo
    @52
    @54
    wceq
    @58
    @53
    @54
    @5
    f1ofo
    @53
    @54
    @5
    forn
    3syl
    sseqtr4d
    @9
    @29
    @5
    funimass1
    syl2anc
    mpd
    @44
    @48
    @5
    @31
    cima
    #
    @14
    @44
    @6
    @29
    @53
    wss
    #
    @48
    @60
    wceq
    @50
    @42
    @61
    @26
    @34
    @29
    cJ
    elssuni
    ad2antrl
    #
    @29
    @5
    cJ
    cK
    @53
    @56
    hmeocls
    syl2anc
    @44
    @60
    @14
    wss
    #
    @33
    @26
    @42
    @30
    @33
    simprrr
    @44
    @51
    @31
    @5
    cdm
    #
    wss
    @63
    @33
    wb
    @59
    @44
    @31
    @53
    @64
    @44
    cJ
    ctop
    wcel
    #
    @61
    @31
    @53
    wss
    @2
    @65
    @6
    @25
    @43
    cJ
    nrmtop
    ad3antrrr
    @62
    @29
    cJ
    @53
    @56
    clsss3
    syl2anc
    @44
    @55
    @64
    @53
    wceq
    @58
    @53
    @54
    @5
    f1odm
    syl
    sseqtr4d
    @31
    @14
    @5
    funimass3
    syl2anc
    mpbird
    eqsstrd
    @16
    @47
    @49
    wa
    vz
    @45
    cK
    @10
    @45
    wceq
    #
    @11
    @47
    @15
    @49
    @10
    @45
    @9
    sseq2
    @66
    @13
    @48
    @14
    @10
    @45
    @12
    fveq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    ralrimivva
    vx
    vy
    vz
    cK
    isnrm
    sylanbrc
    expcom
    exlimiv
    sylbi
    sylbi
end
