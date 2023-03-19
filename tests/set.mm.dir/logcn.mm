include "clog.mm"
include "cres.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "crp.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "wfn.mm"
include "wceq.mm"
include "crn.mm"
include "wf.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "wf1o.mm"
include "logf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "logdmss.mm"
include "fssres.mm"
include "mp2an.mm"
include "ffn.mm"
include "dffn5.mm"
include "mpbi.mm"
include "wcel.mm"
include "cre.mm"
include "fvres.mm"
include "cr.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "logdmn0.mm"
include "logcld.mm"
include "replimd.mm"
include "wne.mm"
include "relog.mm"
include "syl2anc.mm"
include "absrpcld.mm"
include "syl.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "wtru.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "addcn.mm"
include "a1i.mm"
include "crest.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "ssriv.mm"
include "resttopon.mm"
include "absf.mm"
include "feqmptd.mm"
include "syl6eq.mm"
include "wral.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wb.mm"
include "rpssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "abscncf.mm"
include "rescncf.mm"
include "mp2.mm"
include "cncffvrn.mm"
include "mpbir.mm"
include "syl6eqelr.mm"
include "cncfcn.mm"
include "syl6eleq.mm"
include "ssid.mm"
include "cncfss.mm"
include "relogcn.mm"
include "sselii.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "cnmpt11f.mm"
include "syl6eleqr.mm"
include "ccom.mm"
include "imcld.mm"
include "recnd.mm"
include "adantl.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fmptco.mm"
include "logcnlem5.mm"
include "ax-icn.mm"
include "mulc1cncf.mm"
include "mp1i.mm"
include "cncfco.mm"
include "eqeltrrd.mm"
include "cncfmpt2f.mm"
include "trud.mm"
include "eqeltri.mm"

theorem logcn
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( log |` D ) e. ( D -cn-> CC )

  proof
    clog
    cD
    cres
    #
    vx
    cD
    vx
    cv
    #
    cabs
    cfv
    #
    clog
    crp
    cres
    #
    cfv
    #
    ci
    @1
    clog
    cfv
    #
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    cD
    cc
    ccncf
    co
    #
    @0
    vx
    cD
    @1
    @0
    cfv
    #
    cmpt
    #
    @9
    @0
    cD
    wfn
    #
    @0
    @12
    wceq
    cD
    clog
    crn
    #
    @0
    wf
    #
    @13
    cc
    cc0
    csn
    cdif
    #
    @14
    clog
    wf
    #
    cD
    @16
    wss
    @15
    @16
    @14
    clog
    wf1o
    @17
    logf1o
    @16
    @14
    clog
    f1of
    ax-mp
    cD
    logcn.d
    logdmss
    @16
    @14
    cD
    clog
    fssres
    mp2an
    cD
    @14
    @0
    ffn
    ax-mp
    vx
    cD
    @0
    dffn5
    mpbi
    vx
    cD
    @11
    @8
    @1
    cD
    wcel
    #
    @11
    @5
    @5
    cre
    cfv
    #
    @7
    caddc
    co
    @8
    @1
    cD
    clog
    fvres
    @18
    @5
    @18
    @1
    @18
    @1
    cc
    wcel
    #
    @1
    cr
    wcel
    @1
    crp
    wcel
    wi
    @1
    cD
    logcn.d
    ellogdm
    simplbi
    #
    @1
    cD
    logcn.d
    logdmn0
    #
    logcld
    #
    replimd
    @18
    @19
    @4
    @7
    caddc
    @18
    @19
    @2
    clog
    cfv
    #
    @4
    @18
    @20
    @1
    cc0
    wne
    @19
    @24
    wceq
    @21
    @22
    @1
    relog
    syl2anc
    @18
    @2
    crp
    wcel
    @4
    @24
    wceq
    @18
    @1
    @21
    @22
    absrpcld
    #
    @2
    crp
    clog
    fvres
    syl
    eqtr4d
    oveq1d
    3eqtrd
    mpteq2ia
    eqtri
    @9
    @10
    wcel
    wtru
    vx
    @4
    @7
    caddc
    ccnfld
    ctopn
    cfv
    #
    cD
    @26
    eqid
    #
    caddc
    @26
    @26
    ctx
    co
    @26
    ccn
    co
    wcel
    wtru
    @26
    @27
    addcn
    a1i
    wtru
    vx
    cD
    @4
    cmpt
    @26
    cD
    crest
    co
    #
    @26
    ccn
    co
    #
    @10
    wtru
    vx
    @2
    @3
    @28
    @26
    crp
    crest
    co
    #
    @26
    cD
    @28
    cD
    ctopon
    cfv
    wcel
    #
    wtru
    @26
    cc
    ctopon
    cfv
    wcel
    cD
    cc
    wss
    #
    @31
    @26
    @27
    cnfldtopon
    #
    vx
    cD
    cc
    @21
    ssriv
    #
    cD
    @26
    cc
    resttopon
    mp2an
    a1i
    wtru
    vx
    cD
    @2
    cmpt
    #
    cD
    crp
    ccncf
    co
    #
    @28
    @30
    ccn
    co
    #
    wtru
    @35
    cabs
    cD
    cres
    #
    @36
    wtru
    @38
    vx
    cD
    @1
    @38
    cfv
    #
    cmpt
    @35
    wtru
    vx
    cD
    cr
    @38
    cD
    cr
    @38
    wf
    #
    wtru
    cc
    cr
    cabs
    wf
    @32
    @40
    absf
    @34
    cc
    cr
    cD
    cabs
    fssres
    mp2an
    #
    a1i
    feqmptd
    vx
    cD
    @39
    @2
    @1
    cD
    cabs
    fvres
    #
    mpteq2ia
    syl6eq
    @38
    @36
    wcel
    #
    cD
    crp
    @38
    wf
    #
    @44
    @38
    cD
    wfn
    #
    @39
    crp
    wcel
    #
    vx
    cD
    wral
    @40
    @45
    @41
    cD
    cr
    @38
    ffn
    ax-mp
    @46
    vx
    cD
    @18
    @39
    @2
    crp
    @42
    @25
    eqeltrd
    rgen
    vx
    cD
    crp
    @38
    ffnfv
    mpbir2an
    crp
    cc
    wss
    #
    @38
    cD
    cr
    ccncf
    co
    #
    wcel
    #
    @43
    @44
    wb
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    #
    @32
    cabs
    cc
    cr
    ccncf
    co
    wcel
    @49
    @34
    abscncf
    cc
    cr
    cD
    cabs
    rescncf
    mp2
    cD
    cr
    crp
    @38
    cncffvrn
    mp2an
    mpbir
    syl6eqelr
    @32
    @47
    @36
    @37
    wceq
    @34
    @50
    cD
    crp
    @26
    @28
    @30
    @27
    @28
    eqid
    #
    @30
    eqid
    #
    cncfcn
    mp2an
    syl6eleq
    wtru
    @3
    crp
    cc
    ccncf
    co
    #
    @30
    @26
    ccn
    co
    #
    @3
    @53
    wcel
    wtru
    crp
    cr
    ccncf
    co
    #
    @53
    @3
    cr
    cc
    wss
    #
    cc
    cc
    wss
    #
    @55
    @53
    wss
    ax-resscn
    cc
    ssid
    #
    crp
    cr
    cc
    cncfss
    mp2an
    relogcn
    sselii
    a1i
    @47
    @57
    @53
    @54
    wceq
    @50
    @58
    crp
    cc
    @26
    @30
    @26
    @27
    @52
    @26
    cc
    crest
    co
    #
    @26
    @26
    ctop
    wcel
    @59
    @26
    wceq
    @26
    @27
    cnfldtop
    @26
    ctop
    cc
    cc
    @26
    @33
    toponunii
    restid
    ax-mp
    eqcomi
    #
    cncfcn
    mp2an
    syl6eleq
    cnmpt11f
    @32
    @57
    @10
    @29
    wceq
    @34
    @58
    cD
    cc
    @26
    @28
    @26
    @27
    @51
    @60
    cncfcn
    mp2an
    syl6eleqr
    wtru
    vy
    cc
    ci
    vy
    cv
    #
    cmul
    co
    #
    cmpt
    #
    vx
    cD
    @6
    cmpt
    #
    ccom
    vx
    cD
    @7
    cmpt
    @10
    wtru
    vx
    vy
    cD
    cc
    @6
    @62
    @7
    @64
    @63
    @18
    @6
    cc
    wcel
    wtru
    @18
    @6
    @18
    @5
    @23
    imcld
    recnd
    adantl
    wtru
    @64
    eqidd
    wtru
    @63
    eqidd
    @61
    @6
    ci
    cmul
    oveq2
    fmptco
    wtru
    cD
    cc
    cc
    @64
    @63
    @64
    @10
    wcel
    wtru
    @48
    @10
    @64
    @56
    @57
    @48
    @10
    wss
    ax-resscn
    @58
    cD
    cr
    cc
    cncfss
    mp2an
    vx
    cD
    logcn.d
    logcnlem5
    sselii
    a1i
    ci
    cc
    wcel
    @63
    cc
    cc
    ccncf
    co
    wcel
    wtru
    ax-icn
    vy
    ci
    @63
    @63
    eqid
    mulc1cncf
    mp1i
    cncfco
    eqeltrrd
    cncfmpt2f
    trud
    eqeltri
end
