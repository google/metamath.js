include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "creg.mm"
include "wcel.mm"
include "wi.mm"
include "hmph.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "ctop.mm"
include "ccl.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
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
include "cuni.mm"
include "wfn.mm"
include "wf1o.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "ad2antlr.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "3syl.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "regsep.mm"
include "simpllr.mm"
include "hmeoima.mm"
include "sseldd.mm"
include "simprrl.mm"
include "wb.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "imacnvcnv.mm"
include "syl6eleq.mm"
include "wceq.mm"
include "hmeocls.mm"
include "simprrr.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ofun.mm"
include "regtop.mm"
include "clsss3.mm"
include "f1odm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "mpbird.mm"
include "eqsstrd.mm"
include "eleq2.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "isreg.mm"
include "sylanbrc.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem reghmph
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J ~= K -> ( J e. Reg -> K e. Reg ) )

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
    creg
    wcel
    #
    cK
    creg
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
    wcel
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
    @14
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
    @18
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
    @14
    @7
    @14
    cK
    wcel
    #
    @9
    @14
    wcel
    #
    wa
    #
    wa
    #
    @9
    @5
    ccnv
    #
    cfv
    #
    vw
    cv
    #
    wcel
    #
    @26
    cJ
    ccl
    cfv
    cfv
    #
    @24
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
    @23
    @2
    @29
    cJ
    wcel
    #
    @25
    @29
    wcel
    #
    @31
    vw
    cJ
    wrex
    @2
    @6
    @22
    simpll
    #
    @23
    @18
    @20
    @32
    @7
    @18
    @22
    @19
    adantr
    @7
    @20
    @21
    simprl
    @14
    @5
    cJ
    cK
    cnima
    syl2anc
    @23
    @24
    cK
    cuni
    #
    wfn
    #
    @14
    @35
    wss
    #
    @21
    @33
    @23
    cJ
    cuni
    #
    @35
    @5
    wf1o
    #
    @35
    @38
    @24
    wf1o
    @36
    @6
    @39
    @2
    @22
    @5
    cJ
    cK
    @38
    @35
    @38
    eqid
    #
    @35
    eqid
    hmeof1o
    ad2antlr
    #
    @38
    @35
    @5
    f1ocnv
    @35
    @38
    @24
    f1ofn
    3syl
    #
    @20
    @37
    @7
    @21
    @14
    cK
    elssuni
    ad2antrl
    #
    @7
    @20
    @21
    simprr
    #
    @35
    @14
    @24
    @9
    fnfvima
    syl3anc
    vw
    @25
    @29
    cJ
    regsep
    syl3anc
    @23
    @26
    cJ
    wcel
    #
    @31
    wa
    #
    wa
    #
    @5
    @26
    cima
    #
    cK
    wcel
    #
    @9
    @48
    wcel
    #
    @48
    @12
    cfv
    #
    @14
    wss
    #
    @17
    @47
    @6
    @45
    @49
    @2
    @6
    @22
    @46
    simpllr
    #
    @23
    @45
    @31
    simprl
    @26
    @5
    cJ
    cK
    hmeoima
    syl2anc
    @47
    @9
    @24
    ccnv
    @26
    cima
    #
    @48
    @47
    @9
    @54
    wcel
    #
    @9
    @35
    wcel
    #
    @27
    @23
    @56
    @46
    @23
    @14
    @35
    @9
    @43
    @44
    sseldd
    adantr
    @23
    @45
    @27
    @30
    simprrl
    @47
    @36
    @55
    @56
    @27
    wa
    wb
    @23
    @36
    @46
    @42
    adantr
    @35
    @9
    @26
    @24
    elpreima
    syl
    mpbir2and
    @5
    @26
    imacnvcnv
    syl6eleq
    @47
    @51
    @5
    @28
    cima
    #
    @14
    @47
    @6
    @26
    @38
    wss
    #
    @51
    @57
    wceq
    @53
    @45
    @58
    @23
    @31
    @26
    cJ
    elssuni
    ad2antrl
    #
    @26
    @5
    cJ
    cK
    @38
    @40
    hmeocls
    syl2anc
    @47
    @57
    @14
    wss
    #
    @30
    @23
    @45
    @27
    @30
    simprrr
    @47
    @5
    wfun
    #
    @28
    @5
    cdm
    #
    wss
    @60
    @30
    wb
    @47
    @39
    @61
    @23
    @39
    @46
    @41
    adantr
    #
    @38
    @35
    @5
    f1ofun
    syl
    @47
    @28
    @38
    @62
    @47
    cJ
    ctop
    wcel
    #
    @58
    @28
    @38
    wss
    @47
    @2
    @64
    @23
    @2
    @46
    @34
    adantr
    cJ
    regtop
    syl
    @59
    @26
    cJ
    @38
    @40
    clsss3
    syl2anc
    @47
    @39
    @62
    @38
    wceq
    @63
    @38
    @35
    @5
    f1odm
    syl
    sseqtr4d
    @28
    @14
    @5
    funimass3
    syl2anc
    mpbird
    eqsstrd
    @16
    @50
    @52
    wa
    vz
    @48
    cK
    @10
    @48
    wceq
    #
    @11
    @50
    @15
    @52
    @10
    @48
    @9
    eleq2
    @65
    @13
    @51
    @14
    @10
    @48
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
    isreg
    sylanbrc
    expcom
    exlimiv
    sylbi
    sylbi
end
