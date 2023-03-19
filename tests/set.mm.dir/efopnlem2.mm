include "crp.mm"
include "wcel.mm"
include "cpi.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "ce.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cima.mm"
include "cc.mm"
include "cmnf.mm"
include "cioc.mm"
include "cdif.mm"
include "wss.mm"
include "crest.mm"
include "clog.mm"
include "cres.mm"
include "ccnv.mm"
include "cim.mm"
include "cneg.mm"
include "csn.mm"
include "crn.mm"
include "wf1o.mm"
include "wfun.mm"
include "wceq.mm"
include "logf1o.mm"
include "wfn.mm"
include "f1orn.mm"
include "simprbi.mm"
include "funcnvres.mm"
include "mp2b.mm"
include "df-log.mm"
include "cnveqi.mm"
include "wrel.mm"
include "relres.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "eqtri.mm"
include "reseq1i.mm"
include "imassrn.mm"
include "logrn.mm"
include "sseqtri.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "3eqtri.mm"
include "imaeq1i.mm"
include "cioo.mm"
include "cv.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "a1i.mm"
include "0cnd.mm"
include "rpxr.mm"
include "adantr.mm"
include "blssm.mm"
include "syl3anc.mm"
include "sselda.mm"
include "cr.mm"
include "imcld.mm"
include "efopnlem1.mm"
include "wb.mm"
include "pire.mm"
include "abslt.mm"
include "sylancl.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "w3a.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "wf.mm"
include "imf.mm"
include "ffn.mm"
include "elpreima.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "df-ima.mm"
include "wfo.mm"
include "eqid.mm"
include "logf1o2.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl6sseqr.mm"
include "resima2.mm"
include "syl.mm"
include "syl5eq.mm"
include "ccn.mm"
include "ccncf.mm"
include "logcn.mm"
include "difss.mm"
include "ssid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "eleqtri.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "cnima.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "logdmopn.mm"
include "eleqtrri.mm"
include "restopn2.mm"
include "sylib.mm"

theorem efopnlem2
  let cR: class R
  let cJ: class J
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  assume efopn.j: |- J = ( TopOpen ` CCfld )


  assert |- ( ( R e. RR+ /\ R < _pi ) -> ( exp " ( 0 ( ball ` ( abs o. - ) ) R ) ) e. J )

  proof
    cR
    crp
    wcel
    #
    cR
    cpi
    clt
    wbr
    #
    wa
    #
    ce
    cc0
    cR
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cima
    #
    cJ
    wcel
    #
    @5
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    wss
    #
    @2
    @5
    cJ
    @8
    crest
    co
    #
    wcel
    #
    @6
    @9
    wa
    #
    @2
    clog
    @8
    cres
    #
    ccnv
    #
    @4
    cima
    #
    @5
    @10
    @2
    @15
    ce
    clog
    @8
    cima
    #
    cres
    #
    @4
    cima
    #
    @5
    @14
    @17
    @4
    @14
    clog
    ccnv
    #
    @16
    cres
    #
    ce
    cim
    ccnv
    #
    cpi
    cneg
    #
    cpi
    cioc
    co
    cima
    #
    cres
    #
    @16
    cres
    #
    @17
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
    @19
    wfun
    #
    @14
    @20
    wceq
    logf1o
    @28
    clog
    @26
    wfn
    @29
    @26
    clog
    f1orn
    simprbi
    @8
    clog
    funcnvres
    mp2b
    @19
    @24
    @16
    @19
    @24
    ccnv
    #
    ccnv
    #
    @24
    clog
    @30
    df-log
    cnveqi
    @24
    wrel
    @31
    @24
    wceq
    ce
    @23
    relres
    @24
    dfrel2
    mpbi
    eqtri
    reseq1i
    @16
    @23
    wss
    @25
    @17
    wceq
    @16
    @27
    @23
    clog
    @8
    imassrn
    logrn
    sseqtri
    ce
    @16
    @23
    resabs1
    ax-mp
    3eqtri
    imaeq1i
    @2
    @4
    @16
    wss
    @18
    @5
    wceq
    @2
    @4
    @21
    @22
    cpi
    cioo
    co
    #
    cima
    #
    @16
    @2
    vx
    @4
    @33
    @2
    vx
    cv
    #
    @4
    wcel
    #
    @34
    @33
    wcel
    #
    @2
    @35
    wa
    #
    @34
    cc
    wcel
    #
    @34
    cim
    cfv
    #
    @32
    wcel
    #
    @36
    @2
    @4
    cc
    @34
    @2
    @3
    cc
    cxmt
    cfv
    wcel
    #
    cc0
    cc
    wcel
    #
    cR
    cxr
    wcel
    #
    @4
    cc
    wss
    @41
    @2
    cnxmet
    a1i
    #
    @2
    0cnd
    #
    @0
    @43
    @1
    cR
    rpxr
    adantr
    #
    @3
    cc0
    cR
    cc
    blssm
    syl3anc
    sselda
    #
    @37
    @39
    cr
    wcel
    #
    @22
    @39
    clt
    wbr
    #
    @39
    cpi
    clt
    wbr
    #
    @40
    @37
    @34
    @47
    imcld
    #
    @37
    @49
    @50
    @37
    @39
    cabs
    cfv
    cpi
    clt
    wbr
    #
    @49
    @50
    wa
    #
    @34
    cR
    efopnlem1
    @37
    @48
    cpi
    cr
    wcel
    @52
    @53
    wb
    @51
    pire
    @39
    cpi
    abslt
    sylancl
    mpbid
    #
    simpld
    @37
    @49
    @50
    @54
    simprd
    @22
    cxr
    wcel
    cpi
    cxr
    wcel
    @40
    @48
    @49
    @50
    w3a
    wb
    @22
    cpi
    pire
    renegcli
    rexri
    cpi
    pire
    rexri
    @22
    cpi
    @39
    elioo2
    mp2an
    syl3anbrc
    cc
    cr
    cim
    wf
    cim
    cc
    wfn
    @36
    @38
    @40
    wa
    wb
    imf
    cc
    cr
    cim
    ffn
    cc
    @34
    @32
    cim
    elpreima
    mp2b
    sylanbrc
    ex
    ssrdv
    @16
    @13
    crn
    #
    @33
    clog
    @8
    df-ima
    @8
    @33
    @13
    wf1o
    @8
    @33
    @13
    wfo
    @55
    @33
    wceq
    @8
    @8
    eqid
    #
    logf1o2
    @8
    @33
    @13
    f1ofo
    @8
    @33
    @13
    forn
    mp2b
    eqtri
    syl6sseqr
    ce
    @4
    @16
    resima2
    syl
    syl5eq
    @2
    @13
    @10
    cJ
    ccn
    co
    #
    wcel
    @4
    cJ
    wcel
    #
    @15
    @10
    wcel
    @13
    @8
    cc
    ccncf
    co
    #
    @57
    @8
    @56
    logcn
    @8
    cc
    wss
    cc
    cc
    wss
    @59
    @57
    wceq
    cc
    @7
    difss
    cc
    ssid
    @8
    cc
    cJ
    @10
    cJ
    efopn.j
    @10
    eqid
    cJ
    cc
    crest
    co
    #
    cJ
    cJ
    ctop
    wcel
    #
    @60
    cJ
    wceq
    cJ
    efopn.j
    cnfldtop
    #
    cJ
    ctop
    cc
    cc
    cJ
    cJ
    efopn.j
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    eleqtri
    @2
    @41
    @42
    @43
    @58
    @44
    @45
    @46
    @3
    cc0
    cR
    cJ
    cc
    cJ
    efopn.j
    cnfldtopn
    blopn
    syl3anc
    @4
    @13
    @10
    cJ
    cnima
    sylancr
    eqeltrrd
    @61
    @8
    cJ
    wcel
    @11
    @12
    wb
    @62
    @8
    ccnfld
    ctopn
    cfv
    cJ
    @8
    @56
    logdmopn
    efopn.j
    eleqtrri
    @8
    @5
    cJ
    restopn2
    mp2an
    sylib
    simpld
end
