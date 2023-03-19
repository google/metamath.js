include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cxr.mm"
include "wss.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "elssuni.mm"
include "letopuni.mm"
include "syl6sseqr.mm"
include "wel.mm"
include "wa.mm"
include "cr.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cin.mm"
include "cxmt.mm"
include "crest.mm"
include "eqid.mm"
include "rexmet.mm"
include "a1i.mm"
include "ctop.mm"
include "cvv.mm"
include "letop.mm"
include "reex.mm"
include "elrestr.mm"
include "mp3an12.mm"
include "ad2antrr.mm"
include "elin.mm"
include "biimpri.mm"
include "adantll.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cmopn.mm"
include "xrtgioo.mm"
include "tgioo.mm"
include "eqtr3i.mm"
include "mopni2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "xrsxmet.mm"
include "simplr.mm"
include "ressxr.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "syl6eleqr.mm"
include "rpxr.mm"
include "adantl.mm"
include "xrsdsre.mm"
include "eqcomi.mm"
include "blres.mm"
include "xrsblre.mm"
include "sylan2.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtrd.mm"
include "sseq1d.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "syl6bi.mm"
include "reximdva.mm"
include "mpd.mm"
include "wn.mm"
include "c1.mm"
include "1rp.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "sselda.mm"
include "adantr.mm"
include "mp1i.mm"
include "elbl.mm"
include "w3a.mm"
include "simp2.mm"
include "wne.mm"
include "cc0.mm"
include "3ad2ant1.mm"
include "simpl3l.mm"
include "xmetcl.mm"
include "1red.mm"
include "xmetge0.mm"
include "simpl3r.mm"
include "wi.mm"
include "ax-mp.mm"
include "xrltle.mm"
include "sylancl.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "simpr.mm"
include "xrsdsreclb.mm"
include "mpbid.mm"
include "simpld.mm"
include "ex.mm"
include "necon1bd.mm"
include "simp1r.mm"
include "elequ1.mm"
include "syl5ibcom.mm"
include "syld.mm"
include "3expia.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "oveq2.mm"
include "rspcev.mm"
include "sylancr.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "elmopn2.mm"
include "sylanbrc.mm"
include "ssriv.mm"

theorem xrsmopn
  let cD: class D
  let cJ: class J
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cR: class R
  assume xrsxmet.1: |- D = ( dist ` RR*s )
  assume xrsmopn.1: |- J = ( MetOpen ` D )


  assert |- ( ordTop ` <_ ) C_ J

  proof
    vx
    cle
    cordt
    cfv
    #
    cJ
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cxr
    wss
    #
    vy
    cv
    #
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @1
    wss
    #
    vr
    crp
    wrex
    #
    vy
    @1
    wral
    #
    @1
    cJ
    wcel
    #
    @2
    @1
    @0
    cuni
    cxr
    @1
    @0
    elssuni
    letopuni
    syl6sseqr
    #
    @2
    @9
    vy
    @1
    @2
    vy
    vx
    wel
    #
    wa
    #
    @4
    cr
    wcel
    #
    @9
    @14
    @15
    wa
    #
    @4
    @5
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    #
    cres
    #
    cbl
    cfv
    co
    #
    @1
    cr
    cin
    #
    wss
    #
    vr
    crp
    wrex
    #
    @9
    @16
    @18
    cr
    cxmt
    cfv
    wcel
    #
    @20
    @0
    cr
    crest
    co
    #
    wcel
    #
    @4
    @20
    wcel
    #
    @22
    @23
    @16
    @18
    @18
    eqid
    #
    rexmet
    a1i
    @2
    @25
    @13
    @15
    @0
    ctop
    wcel
    cr
    cvv
    wcel
    @2
    @25
    letop
    reex
    @1
    cr
    @0
    ctop
    cvv
    elrestr
    mp3an12
    ad2antrr
    @13
    @15
    @26
    @2
    @26
    @13
    @15
    wa
    @4
    @1
    cr
    elin
    biimpri
    adantll
    vr
    @20
    @18
    @4
    @24
    cr
    cioo
    crn
    ctg
    cfv
    @24
    @18
    cmopn
    cfv
    #
    @24
    @24
    eqid
    xrtgioo
    @18
    @28
    @27
    @28
    eqid
    tgioo
    eqtr3i
    mopni2
    syl3anc
    @16
    @21
    @8
    vr
    crp
    @16
    @5
    crp
    wcel
    #
    wa
    #
    @21
    @7
    @20
    wss
    #
    @8
    @30
    @19
    @7
    @20
    @30
    @19
    @7
    cr
    cin
    #
    @7
    @30
    cD
    cxr
    cxmt
    cfv
    wcel
    #
    @4
    cxr
    cr
    cin
    #
    wcel
    @5
    cxr
    wcel
    #
    @19
    @32
    wceq
    @33
    @30
    cD
    xrsxmet.1
    xrsxmet
    #
    a1i
    @30
    @4
    cr
    @34
    @14
    @15
    @29
    simplr
    cr
    cxr
    wss
    @34
    cr
    wceq
    ressxr
    cr
    cxr
    sseqin2
    mpbi
    syl6eleqr
    @29
    @35
    @16
    @5
    rpxr
    #
    adantl
    @18
    cD
    @4
    @5
    cxr
    cr
    cD
    @17
    cres
    @18
    cD
    xrsxmet.1
    xrsdsre
    eqcomi
    blres
    syl3anc
    @30
    @7
    cr
    wss
    #
    @32
    @7
    wceq
    @15
    @29
    @38
    @14
    @29
    @15
    @35
    @38
    @37
    cD
    @4
    @5
    xrsxmet.1
    xrsblre
    sylan2
    adantll
    @7
    cr
    df-ss
    sylib
    eqtrd
    sseq1d
    @31
    @20
    @1
    wss
    @8
    @1
    cr
    inss1
    @7
    @20
    @1
    sstr
    mpan2
    syl6bi
    reximdva
    mpd
    @14
    @15
    wn
    #
    wa
    #
    c1
    crp
    wcel
    #
    @4
    c1
    @6
    co
    #
    @1
    wss
    #
    @9
    1rp
    @40
    vz
    @42
    @1
    @40
    vz
    cv
    #
    @42
    wcel
    #
    @44
    cxr
    wcel
    #
    @4
    @44
    cD
    co
    #
    c1
    clt
    wbr
    #
    wa
    #
    vz
    vx
    wel
    #
    @40
    @33
    @4
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    @45
    @49
    wb
    @33
    @40
    @36
    a1i
    @14
    @51
    @39
    @2
    @1
    cxr
    @4
    @12
    sselda
    #
    adantr
    @41
    @52
    @40
    1rp
    c1
    rpxr
    #
    mp1i
    @44
    cD
    @4
    c1
    cxr
    elbl
    syl3anc
    @14
    @39
    @49
    @50
    @14
    @39
    @49
    w3a
    #
    @39
    @50
    @14
    @39
    @49
    simp2
    @55
    @39
    @4
    @44
    wceq
    #
    @50
    @55
    @15
    @4
    @44
    @55
    @4
    @44
    wne
    #
    @15
    @55
    @57
    wa
    #
    @15
    @44
    cr
    wcel
    #
    @58
    @47
    cr
    wcel
    #
    @15
    @59
    wa
    #
    @58
    @47
    cxr
    wcel
    #
    c1
    cr
    wcel
    cc0
    @47
    cle
    wbr
    #
    @47
    c1
    cle
    wbr
    #
    @60
    @58
    @33
    @51
    @46
    @62
    @33
    @58
    @36
    a1i
    #
    @55
    @51
    @57
    @14
    @39
    @51
    @49
    @53
    3ad2ant1
    adantr
    #
    @46
    @48
    @14
    @39
    @57
    simpl3l
    #
    @4
    @44
    cD
    cxr
    xmetcl
    syl3anc
    #
    @58
    1red
    @58
    @33
    @51
    @46
    @63
    @65
    @66
    @67
    @4
    @44
    cD
    cxr
    xmetge0
    syl3anc
    @58
    @48
    @64
    @46
    @48
    @14
    @39
    @57
    simpl3r
    @58
    @62
    @52
    @48
    @64
    wi
    @68
    @41
    @52
    1rp
    @54
    ax-mp
    @47
    c1
    xrltle
    sylancl
    mpd
    @47
    c1
    xrrege0
    syl22anc
    @58
    @51
    @46
    @57
    @60
    @61
    wb
    @66
    @67
    @55
    @57
    simpr
    @4
    @44
    cD
    xrsxmet.1
    xrsdsreclb
    syl3anc
    mpbid
    simpld
    ex
    necon1bd
    @55
    @13
    @56
    @50
    @2
    @13
    @39
    @49
    simp1r
    vy
    vz
    vx
    elequ1
    syl5ibcom
    syld
    mpd
    3expia
    sylbid
    ssrdv
    @8
    @43
    vr
    c1
    crp
    @5
    c1
    wceq
    @7
    @42
    @1
    @5
    c1
    @4
    @6
    oveq2
    sseq1d
    rspcev
    sylancr
    pm2.61dan
    ralrimiva
    @33
    @11
    @3
    @10
    wa
    wb
    @36
    vy
    vr
    @1
    cD
    cJ
    cxr
    xrsmopn.1
    elmopn2
    ax-mp
    sylanbrc
    ssriv
end
