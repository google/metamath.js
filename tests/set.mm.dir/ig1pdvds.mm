include "cdr.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "c0g.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "crg.mm"
include "cbs.mm"
include "drngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "eqid.mm"
include "lidlss.mm"
include "3ad2ant2.mm"
include "ig1pcl.mm"
include "3adant3.mm"
include "sseldd.mm"
include "dvdsr01.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eleq2.mm"
include "biimpac.mm"
include "3ad2antl3.mm"
include "elsni.mm"
include "breqtrrd.mm"
include "wne.mm"
include "cr1p.mm"
include "co.mm"
include "cdg1.mm"
include "cdif.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wn.mm"
include "cuc1p.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cmn1.mm"
include "simpr.mm"
include "ig1pval3.mm"
include "syl3anc.mm"
include "simp2d.mm"
include "mon1puc1p.mm"
include "r1pdeglt.mm"
include "simp3d.mm"
include "breqtrd.mm"
include "cxr.mm"
include "wb.mm"
include "wf.mm"
include "deg1xrf.mm"
include "cq1p.mm"
include "cmulr.mm"
include "csg.mm"
include "simp1d.mm"
include "r1pval.mm"
include "q1pcl.mm"
include "lidlmcl.mm"
include "syl22anc.mm"
include "lidlsubcl.mm"
include "eqeltrd.mm"
include "ffvelrn.mm"
include "sylancr.mm"
include "cc0.mm"
include "cuz.mm"
include "ssdifd.mm"
include "imass2.mm"
include "cn0.mm"
include "deg1n0ima.mm"
include "nn0uz.mm"
include "syl6sseq.mm"
include "sstrd.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "c0.mm"
include "lidl0cl.mm"
include "snssd.mm"
include "necomd.mm"
include "pssdifn0.mm"
include "wfn.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ssdifssd.mm"
include "fnimaeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "infssuzcl.mm"
include "xrltnle.mm"
include "mpbid.mm"
include "a1i.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "fnfvima.mm"
include "infssuzle.mm"
include "ex.mm"
include "necon1bd.mm"
include "mpd.mm"
include "dvdsr1p.mm"
include "pm2.61dane.mm"

theorem ig1pdvds
  let c.pa: class .||
  let cP: class P
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  let cX: class X
  assume ig1pval.p: |- P = ( Poly1 ` R )
  assume ig1pval.g: |- G = ( idlGen1p ` R )
  assume ig1pcl.u: |- U = ( LIdeal ` P )
  assume ig1pdvds.d: |- .|| = ( ||r ` P )


  assert |- ( ( R e. DivRing /\ I e. U /\ X e. I ) -> ( G ` I ) .|| X )

  proof
    cR
    cdr
    wcel
    #
    cI
    cU
    wcel
    #
    cX
    cI
    wcel
    #
    w3a
    #
    cI
    cG
    cfv
    #
    cX
    c.pa
    wbr
    #
    cI
    cP
    c0g
    cfv
    #
    csn
    #
    @3
    cI
    @7
    wceq
    #
    wa
    #
    @4
    @6
    cX
    c.pa
    @3
    @4
    @6
    c.pa
    wbr
    #
    @8
    @3
    cP
    crg
    wcel
    #
    @4
    cP
    cbs
    cfv
    #
    wcel
    #
    @10
    @0
    @1
    @11
    @2
    @0
    cR
    crg
    wcel
    #
    @11
    cR
    drngring
    #
    cP
    cR
    ig1pval.p
    ply1ring
    #
    syl
    3ad2ant1
    @3
    cI
    @12
    @4
    @1
    @0
    cI
    @12
    wss
    #
    @2
    @12
    cI
    cU
    cP
    @12
    eqid
    #
    ig1pcl.u
    lidlss
    #
    3ad2ant2
    @0
    @1
    @4
    cI
    wcel
    #
    @2
    cP
    cR
    cU
    cG
    cI
    ig1pval.p
    ig1pval.g
    ig1pcl.u
    ig1pcl
    3adant3
    sseldd
    @12
    c.pa
    cP
    @4
    @6
    @18
    ig1pdvds.d
    @6
    eqid
    #
    dvdsr01
    syl2anc
    adantr
    @9
    cX
    @7
    wcel
    #
    cX
    @6
    wceq
    @2
    @0
    @8
    @22
    @1
    @8
    @2
    @22
    cI
    @7
    cX
    eleq2
    biimpac
    3ad2antl3
    cX
    @6
    elsni
    syl
    breqtrrd
    @3
    cI
    @7
    wne
    #
    wa
    #
    @5
    cX
    @4
    cR
    cr1p
    cfv
    #
    co
    #
    @6
    wceq
    #
    @24
    cR
    cdg1
    cfv
    #
    cI
    @7
    cdif
    #
    cima
    #
    cr
    clt
    cinf
    #
    @26
    @28
    cfv
    #
    cle
    wbr
    #
    wn
    #
    @27
    @24
    @32
    @31
    clt
    wbr
    #
    @34
    @24
    @32
    @4
    @28
    cfv
    #
    @31
    clt
    @24
    @14
    cX
    @12
    wcel
    #
    @4
    cR
    cuc1p
    cfv
    #
    wcel
    #
    @32
    @36
    clt
    wbr
    @24
    @0
    @14
    @0
    @1
    @2
    @23
    simpl1
    #
    @15
    syl
    #
    @24
    cI
    @12
    cX
    @24
    @1
    @17
    @0
    @1
    @2
    @23
    simpl2
    #
    @19
    syl
    #
    @0
    @1
    @2
    @23
    simpl3
    #
    sseldd
    #
    @24
    @14
    @4
    cR
    cmn1
    cfv
    #
    wcel
    #
    @39
    @41
    @24
    @20
    @47
    @36
    @31
    wceq
    #
    @24
    @0
    @1
    @23
    @20
    @47
    @48
    w3a
    @40
    @42
    @3
    @23
    simpr
    #
    @28
    cP
    cR
    cU
    cG
    cI
    @46
    @6
    ig1pval.p
    ig1pval.g
    @21
    ig1pcl.u
    @28
    eqid
    #
    @46
    eqid
    #
    ig1pval3
    syl3anc
    #
    simp2d
    @38
    cR
    @46
    @4
    @38
    eqid
    #
    @51
    mon1puc1p
    syl2anc
    #
    @12
    @38
    @28
    cP
    cR
    @25
    cX
    @4
    @25
    eqid
    #
    ig1pval.p
    @18
    @53
    @50
    r1pdeglt
    syl3anc
    @24
    @20
    @47
    @48
    @52
    simp3d
    breqtrd
    @24
    @32
    cxr
    wcel
    #
    @31
    cxr
    wcel
    @35
    @34
    wb
    @24
    @12
    cxr
    @28
    wf
    #
    @26
    @12
    wcel
    @56
    @12
    @28
    cP
    cR
    @50
    ig1pval.p
    @18
    deg1xrf
    #
    @24
    cI
    @12
    @26
    @43
    @24
    @26
    cX
    cX
    @4
    cR
    cq1p
    cfv
    #
    co
    #
    @4
    cP
    cmulr
    cfv
    #
    co
    #
    cP
    csg
    cfv
    #
    co
    #
    cI
    @24
    @37
    @13
    @26
    @64
    wceq
    @45
    @24
    cI
    @12
    @4
    @43
    @24
    @20
    @47
    @48
    @52
    simp1d
    #
    sseldd
    @12
    cP
    @59
    cR
    @61
    @25
    cX
    @4
    @63
    @55
    ig1pval.p
    @18
    @59
    eqid
    #
    @61
    eqid
    #
    @63
    eqid
    #
    r1pval
    syl2anc
    @24
    @11
    @1
    @2
    @62
    cI
    wcel
    #
    @64
    cI
    wcel
    @24
    @14
    @11
    @41
    @16
    syl
    #
    @42
    @44
    @24
    @11
    @1
    @60
    @12
    wcel
    #
    @20
    @69
    @70
    @42
    @24
    @14
    @37
    @39
    @71
    @41
    @45
    @54
    @12
    @38
    cP
    @59
    cR
    cX
    @4
    @66
    ig1pval.p
    @18
    @53
    q1pcl
    syl3anc
    @65
    @12
    cP
    @61
    cU
    cI
    @60
    @4
    ig1pcl.u
    @18
    @67
    lidlmcl
    syl22anc
    cP
    cU
    cI
    @63
    cX
    @62
    ig1pcl.u
    @68
    lidlsubcl
    syl22anc
    eqeltrd
    #
    sseldd
    @12
    cxr
    @26
    @28
    ffvelrn
    sylancr
    @24
    @30
    cxr
    @31
    @24
    @30
    cc0
    cuz
    cfv
    #
    cxr
    @24
    @30
    @28
    @12
    @7
    cdif
    #
    cima
    #
    @73
    @24
    @29
    @74
    wss
    @30
    @75
    wss
    @24
    cI
    @12
    @7
    @43
    ssdifd
    @29
    @74
    @28
    imass2
    syl
    @24
    @75
    cn0
    @73
    @24
    @14
    @75
    cn0
    wss
    @41
    @12
    @28
    cP
    cR
    @6
    @50
    ig1pval.p
    @21
    @18
    deg1n0ima
    syl
    nn0uz
    syl6sseq
    sstrd
    #
    @73
    cz
    cxr
    cc0
    uzssz
    cz
    cr
    cxr
    zssre
    ressxr
    sstri
    sstri
    syl6ss
    @24
    @30
    @73
    wss
    #
    @30
    c0
    wne
    #
    @31
    @30
    wcel
    @76
    @24
    @78
    @29
    c0
    wne
    #
    @24
    @7
    cI
    wss
    @7
    cI
    wne
    @79
    @24
    @6
    cI
    @24
    @11
    @1
    @6
    cI
    wcel
    @70
    @42
    cP
    cU
    cI
    @6
    ig1pcl.u
    @21
    lidl0cl
    syl2anc
    snssd
    @24
    cI
    @7
    @49
    necomd
    @7
    cI
    pssdifn0
    syl2anc
    @24
    @30
    c0
    @29
    c0
    @24
    @28
    @12
    wfn
    #
    @29
    @12
    wss
    #
    @30
    c0
    wceq
    @29
    c0
    wceq
    wb
    @57
    @80
    @58
    @12
    cxr
    @28
    ffn
    ax-mp
    #
    @24
    cI
    @12
    @7
    @43
    ssdifssd
    #
    @12
    @29
    @28
    fnimaeq0
    sylancr
    necon3bid
    mpbird
    @30
    cc0
    infssuzcl
    syl2anc
    sseldd
    @32
    @31
    xrltnle
    syl2anc
    mpbid
    @24
    @33
    @26
    @6
    @24
    @26
    @6
    wne
    #
    @33
    @24
    @84
    wa
    #
    @77
    @32
    @30
    wcel
    #
    @33
    @24
    @77
    @84
    @76
    adantr
    @85
    @80
    @81
    @26
    @29
    wcel
    #
    @86
    @80
    @85
    @82
    a1i
    @24
    @81
    @84
    @83
    adantr
    @85
    @26
    cI
    wcel
    #
    @84
    @87
    @24
    @88
    @84
    @72
    adantr
    @24
    @84
    simpr
    @26
    cI
    @6
    eldifsn
    sylanbrc
    @12
    @29
    @28
    @26
    fnfvima
    syl3anc
    @32
    @30
    cc0
    infssuzle
    syl2anc
    ex
    necon1bd
    mpd
    @24
    @14
    @37
    @39
    @5
    @27
    wb
    @41
    @45
    @54
    @12
    @38
    c.pa
    cP
    cR
    @25
    cX
    @4
    @6
    ig1pval.p
    ig1pdvds.d
    @18
    @53
    @21
    @55
    dvdsr1p
    syl3anc
    mpbird
    pm2.61dane
end
