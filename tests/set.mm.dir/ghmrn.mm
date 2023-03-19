include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "crn.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "wf.mm"
include "eqid.mm"
include "ghmf.mm"
include "frn.mm"
include "syl.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "grpbn0.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "w3a.mm"
include "ghmlin.mm"
include "wfn.mm"
include "ffn.mm"
include "3ad2ant1.mm"
include "grpcl.mm"
include "syl3an1.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ralrn.mm"
include "adantr.mm"
include "mpbird.mm"
include "ghminv.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "jca.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "ghmgrp2.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem ghmrn
  let cS: class S
  let cT: class T
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( F e. ( S GrpHom T ) -> ran F e. ( SubGrp ` T ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cF
    crn
    #
    cT
    csubg
    cfv
    wcel
    #
    @1
    cT
    cbs
    cfv
    #
    wss
    #
    @1
    c0
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    cT
    cplusg
    cfv
    #
    co
    #
    @1
    wcel
    #
    vb
    @1
    wral
    #
    @6
    cT
    cminusg
    cfv
    #
    cfv
    #
    @1
    wcel
    #
    wa
    #
    va
    @1
    wral
    #
    @0
    cS
    cbs
    cfv
    #
    @3
    cF
    wf
    #
    @4
    cS
    cT
    cF
    @17
    @3
    @17
    eqid
    #
    @3
    eqid
    #
    ghmf
    #
    @17
    @3
    cF
    frn
    syl
    @0
    cF
    cdm
    #
    c0
    wne
    @5
    @0
    @22
    @17
    c0
    @0
    @18
    @22
    @17
    wceq
    @21
    @17
    @3
    cF
    fdm
    syl
    @0
    cS
    cgrp
    wcel
    #
    @17
    c0
    wne
    cS
    cT
    cF
    ghmgrp1
    #
    @17
    cS
    @19
    grpbn0
    syl
    eqnetrd
    @22
    c0
    @1
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    @0
    @16
    vc
    cv
    #
    cF
    cfv
    #
    @7
    @8
    co
    #
    @1
    wcel
    #
    vb
    @1
    wral
    #
    @26
    @12
    cfv
    #
    @1
    wcel
    #
    wa
    #
    vc
    @17
    wral
    #
    @0
    @32
    vc
    @17
    @0
    @25
    @17
    wcel
    #
    wa
    #
    @29
    @31
    @35
    @29
    @26
    @6
    cF
    cfv
    #
    @8
    co
    #
    @1
    wcel
    #
    va
    @17
    wral
    #
    @35
    @38
    va
    @17
    @0
    @34
    @6
    @17
    wcel
    #
    @38
    @0
    @34
    @40
    w3a
    #
    @25
    @6
    cS
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @37
    @1
    @42
    @8
    cS
    cT
    @25
    cF
    @6
    @17
    @19
    @42
    eqid
    #
    @8
    eqid
    #
    ghmlin
    @41
    cF
    @17
    wfn
    #
    @43
    @17
    wcel
    #
    @44
    @1
    wcel
    @0
    @34
    @47
    @40
    @0
    @18
    @47
    @21
    @17
    @3
    cF
    ffn
    syl
    #
    3ad2ant1
    @0
    @23
    @34
    @40
    @48
    @24
    @17
    @42
    cS
    @25
    @6
    @19
    @45
    grpcl
    syl3an1
    @17
    @43
    cF
    fnfvelrn
    syl2anc
    eqeltrrd
    3expia
    ralrimiv
    @0
    @29
    @39
    wb
    #
    @34
    @0
    @47
    @50
    @49
    @28
    @38
    vb
    va
    @17
    cF
    @7
    @36
    wceq
    @27
    @37
    @1
    @7
    @36
    @26
    @8
    oveq2
    eleq1d
    ralrn
    syl
    adantr
    mpbird
    @35
    @25
    cS
    cminusg
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    @30
    @1
    @17
    cS
    cT
    cF
    @51
    @12
    @25
    @19
    @51
    eqid
    #
    @12
    eqid
    #
    ghminv
    @35
    @47
    @52
    @17
    wcel
    #
    @53
    @1
    wcel
    @0
    @47
    @34
    @49
    adantr
    @0
    @23
    @34
    @56
    @24
    @17
    cS
    @51
    @25
    @19
    @54
    grpinvcl
    sylan
    @17
    @52
    cF
    fnfvelrn
    syl2anc
    eqeltrrd
    jca
    ralrimiva
    @0
    @47
    @16
    @33
    wb
    @49
    @15
    @32
    va
    vc
    @17
    cF
    @6
    @26
    wceq
    #
    @11
    @29
    @14
    @31
    @57
    @10
    @28
    vb
    @1
    @57
    @9
    @27
    @1
    @6
    @26
    @7
    @8
    oveq1
    eleq1d
    ralbidv
    @57
    @13
    @30
    @1
    @6
    @26
    @12
    fveq2
    eleq1d
    anbi12d
    ralrn
    syl
    mpbird
    @0
    cT
    cgrp
    wcel
    @2
    @4
    @5
    @16
    w3a
    wb
    cS
    cT
    cF
    ghmgrp2
    va
    vb
    @3
    @8
    @1
    cT
    @12
    @20
    @46
    @55
    issubg2
    syl
    mpbir3and
end
