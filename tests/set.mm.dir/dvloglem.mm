include "clog.mm"
include "cima.mm"
include "cim.mm"
include "ccnv.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "wral.mm"
include "wb.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "crn.mm"
include "wf1o.mm"
include "logf1o.mm"
include "f1ofun.mm"
include "ax-mp.mm"
include "logdmss.mm"
include "wceq.mm"
include "f1odm.mm"
include "sseqtr4i.mm"
include "funimass4.mm"
include "mp2an.mm"
include "cr.mm"
include "crp.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "logdmn0.mm"
include "logcld.mm"
include "clt.mm"
include "wbr.mm"
include "imcld.mm"
include "cle.mm"
include "logimcld.mm"
include "simpld.mm"
include "wne.mm"
include "wn.mm"
include "logdmnrp.mm"
include "lognegb.mm"
include "syl2anc.mm"
include "necon3bbid.mm"
include "mpbid.mm"
include "necomd.mm"
include "pire.mm"
include "a1i.mm"
include "simprd.mm"
include "leltned.mm"
include "mpbird.mm"
include "cxr.mm"
include "w3a.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioo2.mm"
include "syl3anbrc.mm"
include "wf.mm"
include "wfn.mm"
include "wa.mm"
include "imf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "mprgbir.mm"
include "ce.mm"
include "cioc.mm"
include "df-ioo.mm"
include "df-ioc.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxssixx.mm"
include "imass2.mm"
include "logrn.mm"
include "sseli.mm"
include "logef.mm"
include "syl.mm"
include "cmnf.mm"
include "efcl.mm"
include "adantr.mm"
include "sylbi.mm"
include "simprbi.mm"
include "eliooord.mm"
include "ltned.mm"
include "fveq2d.mm"
include "simpr.mm"
include "mnfxr.mm"
include "0re.mm"
include "elioc2.mm"
include "sylib.mm"
include "simp1d.mm"
include "renegcld.mm"
include "efne0.mm"
include "0red.mm"
include "simp3d.mm"
include "lt0neg1d.mm"
include "elrpd.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "eldifd.mm"
include "syl6eleqr.mm"
include "funfvima2.mm"
include "eqeltrrd.mm"
include "ssriv.mm"
include "eqssi.mm"
include "ctg.mm"
include "ccn.mm"
include "ccncf.mm"
include "imcncf.mm"
include "ssid.mm"
include "ax-resscn.mm"
include "eqid.mm"
include "crest.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "tgioo2.mm"
include "cncfcn.mm"
include "eleqtri.mm"
include "iooretop.mm"
include "cnima.mm"
include "eqeltri.mm"

theorem dvloglem
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( log " D ) e. ( TopOpen ` CCfld )

  proof
    clog
    cD
    cima
    #
    cim
    ccnv
    #
    cpi
    cneg
    #
    cpi
    cioo
    co
    #
    cima
    #
    ccnfld
    ctopn
    cfv
    #
    @0
    @4
    @0
    @4
    wss
    #
    vx
    cv
    #
    clog
    cfv
    #
    @4
    wcel
    #
    vx
    cD
    clog
    wfun
    #
    cD
    clog
    cdm
    #
    wss
    #
    @6
    @9
    vx
    cD
    wral
    wb
    cc
    cc0
    csn
    cdif
    #
    clog
    crn
    #
    clog
    wf1o
    #
    @10
    logf1o
    @13
    @14
    clog
    f1ofun
    ax-mp
    #
    cD
    @13
    @11
    cD
    logcn.d
    logdmss
    @15
    @11
    @13
    wceq
    logf1o
    @13
    @14
    clog
    f1odm
    ax-mp
    sseqtr4i
    #
    vx
    cD
    @4
    clog
    funimass4
    mp2an
    @7
    cD
    wcel
    #
    @8
    cc
    wcel
    #
    @8
    cim
    cfv
    #
    @3
    wcel
    #
    @9
    @18
    @7
    @18
    @7
    cc
    wcel
    #
    @7
    cr
    wcel
    @7
    crp
    wcel
    wi
    @7
    cD
    logcn.d
    ellogdm
    simplbi
    #
    @7
    cD
    logcn.d
    logdmn0
    #
    logcld
    #
    @18
    @20
    cr
    wcel
    #
    @2
    @20
    clt
    wbr
    #
    @20
    cpi
    clt
    wbr
    #
    @21
    @18
    @8
    @25
    imcld
    #
    @18
    @27
    @20
    cpi
    cle
    wbr
    #
    @18
    @7
    @23
    @24
    logimcld
    #
    simpld
    @18
    @28
    cpi
    @20
    wne
    @18
    @20
    cpi
    @18
    @7
    cneg
    crp
    wcel
    #
    wn
    @20
    cpi
    wne
    @7
    cD
    logcn.d
    logdmnrp
    @18
    @32
    @20
    cpi
    @18
    @22
    @7
    cc0
    wne
    @32
    @20
    cpi
    wceq
    wb
    @23
    @24
    @7
    lognegb
    syl2anc
    necon3bbid
    mpbid
    necomd
    @18
    @20
    cpi
    @29
    cpi
    cr
    wcel
    @18
    pire
    a1i
    @18
    @27
    @30
    @31
    simprd
    leltned
    mpbird
    @2
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    @21
    @26
    @27
    @28
    w3a
    wb
    @2
    cpi
    pire
    renegcli
    rexri
    cpi
    pire
    rexri
    @2
    cpi
    @20
    elioo2
    mp2an
    syl3anbrc
    cc
    cr
    cim
    wf
    #
    cim
    cc
    wfn
    #
    @9
    @19
    @21
    wa
    wb
    imf
    cc
    cr
    cim
    ffn
    #
    cc
    @8
    @3
    cim
    elpreima
    mp2b
    sylanbrc
    mprgbir
    vx
    @4
    @0
    @7
    @4
    wcel
    #
    @7
    ce
    cfv
    #
    clog
    cfv
    #
    @7
    @0
    @37
    @7
    @14
    wcel
    @39
    @7
    wceq
    #
    @4
    @14
    @7
    @4
    @1
    @2
    cpi
    cioc
    co
    #
    cima
    #
    @14
    @3
    @41
    wss
    @4
    @42
    wss
    vx
    vy
    vz
    vw
    @2
    cpi
    cioc
    clt
    clt
    clt
    cle
    cioo
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-ioc
    @33
    vw
    cv
    #
    cxr
    wcel
    wa
    @2
    @43
    clt
    wbr
    idd
    @43
    cpi
    xrltle
    ixxssixx
    @3
    @41
    @1
    imass2
    ax-mp
    logrn
    sseqtr4i
    sseli
    @7
    logef
    syl
    #
    @37
    @38
    cD
    wcel
    #
    @39
    @0
    wcel
    #
    @37
    @38
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    cD
    @37
    @38
    cc
    @47
    @37
    @22
    @7
    cim
    cfv
    #
    @3
    wcel
    #
    wa
    #
    @38
    cc
    wcel
    #
    @34
    @35
    @37
    @50
    wb
    imf
    @36
    cc
    @7
    @3
    cim
    elpreima
    mp2b
    #
    @22
    @51
    @49
    @7
    efcl
    adantr
    sylbi
    #
    @37
    @48
    cpi
    wne
    @38
    @47
    wcel
    #
    wn
    @37
    @48
    cpi
    @37
    @7
    @37
    @22
    @49
    @52
    simplbi
    #
    imcld
    @37
    @2
    @48
    clt
    wbr
    #
    @48
    cpi
    clt
    wbr
    #
    @37
    @49
    @56
    @57
    wa
    @37
    @22
    @49
    @52
    simprbi
    @48
    @2
    cpi
    eliooord
    syl
    simprd
    ltned
    @37
    @54
    @48
    cpi
    @37
    @54
    @48
    cpi
    wceq
    @37
    @54
    wa
    #
    @39
    cim
    cfv
    #
    @48
    cpi
    @58
    @39
    @7
    cim
    @37
    @40
    @54
    @44
    adantr
    fveq2d
    @58
    @38
    cneg
    #
    crp
    wcel
    #
    @59
    cpi
    wceq
    #
    @58
    @60
    @58
    @38
    @58
    @38
    cr
    wcel
    #
    cmnf
    @38
    clt
    wbr
    #
    @38
    cc0
    cle
    wbr
    #
    @58
    @54
    @63
    @64
    @65
    w3a
    #
    @37
    @54
    simpr
    cmnf
    cxr
    wcel
    cc0
    cr
    wcel
    @54
    @66
    wb
    mnfxr
    0re
    cmnf
    cc0
    @38
    elioc2
    mp2an
    sylib
    #
    simp1d
    #
    renegcld
    @58
    @38
    cc0
    clt
    wbr
    #
    cc0
    @60
    clt
    wbr
    @58
    @69
    cc0
    @38
    wne
    @58
    @38
    cc0
    @37
    @38
    cc0
    wne
    #
    @54
    @37
    @22
    @70
    @55
    @7
    efne0
    syl
    #
    adantr
    necomd
    @58
    @38
    cc0
    @68
    @58
    0red
    @58
    @63
    @64
    @65
    @67
    simp3d
    leltned
    mpbird
    @58
    @38
    @68
    lt0neg1d
    mpbid
    elrpd
    @37
    @61
    @62
    wb
    #
    @54
    @37
    @51
    @70
    @72
    @53
    @71
    @38
    lognegb
    syl2anc
    adantr
    mpbid
    eqtr3d
    ex
    necon3ad
    mpd
    eldifd
    logcn.d
    syl6eleqr
    @10
    @12
    @45
    @46
    wi
    @16
    @17
    cD
    @38
    clog
    funfvima2
    mp2an
    syl
    eqeltrrd
    ssriv
    eqssi
    cim
    @5
    cioo
    crn
    ctg
    cfv
    #
    ccn
    co
    #
    wcel
    @3
    @73
    wcel
    @4
    @5
    wcel
    cim
    cc
    cr
    ccncf
    co
    #
    @74
    imcncf
    cc
    cc
    wss
    cr
    cc
    wss
    @75
    @74
    wceq
    cc
    ssid
    ax-resscn
    cc
    cr
    @5
    @5
    @73
    @5
    eqid
    #
    @5
    cc
    crest
    co
    #
    @5
    @5
    ctop
    wcel
    @77
    @5
    wceq
    @5
    @76
    cnfldtop
    @5
    ctop
    cc
    cc
    @5
    @5
    @76
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    @5
    @76
    tgioo2
    cncfcn
    mp2an
    eleqtri
    @2
    cpi
    iooretop
    @3
    cim
    @5
    @73
    cnima
    mp2an
    eqeltri
end
