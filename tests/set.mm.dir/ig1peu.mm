include "cdr.mm"
include "wcel.mm"
include "csn.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cdif.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cc0.mm"
include "cuz.mm"
include "wss.mm"
include "c0.mm"
include "cn0.mm"
include "cbs.mm"
include "eqid.mm"
include "lidlss.mm"
include "3ad2ant2.mm"
include "ssdifd.mm"
include "imass2.mm"
include "syl.mm"
include "crg.mm"
include "drngring.mm"
include "3ad2ant1.mm"
include "deg1n0ima.mm"
include "sstrd.mm"
include "nn0uz.mm"
include "syl6sseq.mm"
include "ply1ring.mm"
include "simp2.mm"
include "lidl0cl.mm"
include "syl2anc.mm"
include "snssd.mm"
include "simp3.mm"
include "necomd.mm"
include "pssdifn0.mm"
include "wfn.mm"
include "wb.mm"
include "cxr.mm"
include "wf.mm"
include "deg1xrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "a1i.mm"
include "ssdifssd.mm"
include "fnimaeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "infssuzcl.mm"
include "fvelimab.mm"
include "mpbid.mm"
include "cco1.mm"
include "cinvr.mm"
include "cascl.mm"
include "cmulr.mm"
include "co.mm"
include "adantr.mm"
include "simpl2.mm"
include "ply1sclf.mm"
include "cui.mm"
include "cuc1p.mm"
include "simpl1.mm"
include "sselda.mm"
include "eldifsni.mm"
include "adantl.mm"
include "drnguc1p.mm"
include "syl3anc.mm"
include "uc1pldg.mm"
include "unitinvcl.mm"
include "unitcl.mm"
include "ffvelrnd.mm"
include "eldifi.mm"
include "lidlmcl.mm"
include "syl22anc.mm"
include "uc1pmon1p.mm"
include "elind.mm"
include "crlreg.mm"
include "unitrrg.mm"
include "sseldd.mm"
include "deg1mul3.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "csg.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "inss2.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "deg1submon1p.mm"
include "ex.mm"
include "cle.mm"
include "wn.mm"
include "inss1.mm"
include "lidlsubcl.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "fnfvima.mm"
include "infssuzle.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "sstri.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl5ss.mm"
include "grpsubcl.mm"
include "deg1xrcl.mm"
include "xrlenlt.mm"
include "sylibd.mm"
include "necon4ad.mm"
include "syld.mm"
include "grpsubeq0.mm"
include "ralrimivva.mm"
include "reu4.mm"

theorem ig1peu
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let vg: setvar g
  let cI: class I
  let cM: class M
  let c.0: class .0.
  let vh: setvar h
  assume ig1peu.p: |- P = ( Poly1 ` R )
  assume ig1peu.u: |- U = ( LIdeal ` P )
  assume ig1peu.z: |- .0. = ( 0g ` P )
  assume ig1peu.m: |- M = ( Monic1p ` R )
  assume ig1peu.d: |- D = ( deg1 ` R )

  disjoint D g
  disjoint I g
  disjoint M g
  disjoint P g
  disjoint R g
  disjoint U g
  disjoint .0. g
  disjoint D h
  disjoint g h
  disjoint I h
  disjoint M h
  disjoint R h
  disjoint U h
  disjoint .0. h
  assert |- ( ( R e. DivRing /\ I e. U /\ I =/= { .0. } ) -> E! g e. ( I i^i M ) ( D ` g ) = inf ( ( D " ( I \ { .0. } ) ) , RR , < ) )

  proof
    cR
    cdr
    wcel
    #
    cI
    cU
    wcel
    #
    cI
    c.0
    csn
    #
    wne
    #
    w3a
    #
    vg
    cv
    #
    cD
    cfv
    #
    cD
    cI
    @2
    cdif
    #
    cima
    #
    cr
    clt
    cinf
    #
    wceq
    #
    vg
    cI
    cM
    cin
    #
    wrex
    #
    @10
    vh
    cv
    #
    cD
    cfv
    #
    @9
    wceq
    #
    wa
    #
    @5
    @13
    wceq
    #
    wi
    #
    vh
    @11
    wral
    vg
    @11
    wral
    @10
    vg
    @11
    wreu
    @4
    @15
    vh
    @7
    wrex
    #
    @12
    @4
    @9
    @8
    wcel
    #
    @19
    @4
    @8
    cc0
    cuz
    cfv
    #
    wss
    #
    @8
    c0
    wne
    #
    @20
    @4
    @8
    cn0
    @21
    @4
    @8
    cD
    cP
    cbs
    cfv
    #
    @2
    cdif
    #
    cima
    #
    cn0
    @4
    @7
    @25
    wss
    @8
    @26
    wss
    @4
    cI
    @24
    @2
    @1
    @0
    cI
    @24
    wss
    @3
    @24
    cI
    cU
    cP
    @24
    eqid
    #
    ig1peu.u
    lidlss
    3ad2ant2
    #
    ssdifd
    @7
    @25
    cD
    imass2
    syl
    @4
    cR
    crg
    wcel
    #
    @26
    cn0
    wss
    @0
    @1
    @29
    @3
    cR
    drngring
    3ad2ant1
    #
    @24
    cD
    cP
    cR
    c.0
    ig1peu.d
    ig1peu.p
    ig1peu.z
    @27
    deg1n0ima
    syl
    sstrd
    nn0uz
    syl6sseq
    #
    @4
    @23
    @7
    c0
    wne
    #
    @4
    @2
    cI
    wss
    @2
    cI
    wne
    @32
    @4
    c.0
    cI
    @4
    cP
    crg
    wcel
    #
    @1
    c.0
    cI
    wcel
    @4
    @29
    @33
    @30
    cP
    cR
    ig1peu.p
    ply1ring
    syl
    #
    @0
    @1
    @3
    simp2
    cP
    cU
    cI
    c.0
    ig1peu.u
    ig1peu.z
    lidl0cl
    syl2anc
    snssd
    @4
    cI
    @2
    @0
    @1
    @3
    simp3
    necomd
    @2
    cI
    pssdifn0
    syl2anc
    @4
    @8
    c0
    @7
    c0
    @4
    cD
    @24
    wfn
    #
    @7
    @24
    wss
    #
    @8
    c0
    wceq
    @7
    c0
    wceq
    wb
    @35
    @4
    @24
    cxr
    cD
    wf
    #
    @35
    @24
    cD
    cP
    cR
    ig1peu.d
    ig1peu.p
    @27
    deg1xrf
    #
    @24
    cxr
    cD
    ffn
    ax-mp
    #
    a1i
    #
    @4
    cI
    @24
    @2
    @28
    ssdifssd
    #
    @24
    @7
    cD
    fnimaeq0
    syl2anc
    necon3bid
    mpbird
    @8
    cc0
    infssuzcl
    syl2anc
    #
    @4
    @35
    @36
    @20
    @19
    wb
    @40
    @41
    vh
    @24
    @7
    @9
    cD
    fvelimab
    syl2anc
    mpbid
    @4
    @15
    @12
    vh
    @7
    @4
    @13
    @7
    wcel
    #
    wa
    #
    @6
    @14
    wceq
    #
    vg
    @11
    wrex
    #
    @15
    @12
    @44
    @14
    @13
    cco1
    cfv
    cfv
    #
    cR
    cinvr
    cfv
    #
    cfv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    @13
    cP
    cmulr
    cfv
    #
    co
    #
    @11
    wcel
    @53
    cD
    cfv
    #
    @14
    wceq
    #
    @46
    @44
    cI
    cM
    @53
    @44
    @33
    @1
    @51
    @24
    wcel
    @13
    cI
    wcel
    #
    @53
    cI
    wcel
    @4
    @33
    @43
    @34
    adantr
    @0
    @1
    @3
    @43
    simpl2
    @44
    cR
    cbs
    cfv
    #
    @24
    @49
    @50
    @44
    @29
    @57
    @24
    @50
    wf
    @4
    @29
    @43
    @30
    adantr
    #
    @50
    @24
    cP
    cR
    @57
    ig1peu.p
    @50
    eqid
    #
    @57
    eqid
    #
    @27
    ply1sclf
    syl
    @44
    @49
    cR
    cui
    cfv
    #
    wcel
    #
    @49
    @57
    wcel
    @44
    @29
    @47
    @61
    wcel
    #
    @62
    @58
    @44
    @13
    cR
    cuc1p
    cfv
    #
    wcel
    #
    @63
    @44
    @0
    @13
    @24
    wcel
    #
    @13
    c.0
    wne
    #
    @65
    @0
    @1
    @3
    @43
    simpl1
    @4
    @7
    @24
    @13
    @41
    sselda
    #
    @43
    @67
    @4
    @13
    cI
    c.0
    eldifsni
    adantl
    @24
    @64
    cP
    cR
    @13
    c.0
    ig1peu.p
    @27
    ig1peu.z
    @64
    eqid
    #
    drnguc1p
    syl3anc
    #
    @64
    cD
    cR
    @61
    @13
    ig1peu.d
    @61
    eqid
    #
    @69
    uc1pldg
    syl
    cR
    @61
    @48
    @47
    @71
    @48
    eqid
    #
    unitinvcl
    syl2anc
    #
    @57
    cR
    @61
    @49
    @60
    @71
    unitcl
    syl
    ffvelrnd
    @43
    @56
    @4
    @13
    cI
    @2
    eldifi
    adantl
    @24
    cP
    @52
    cU
    cI
    @51
    @13
    ig1peu.u
    @27
    @52
    eqid
    #
    lidlmcl
    syl22anc
    @44
    @29
    @65
    @53
    cM
    wcel
    @58
    @70
    @50
    @64
    cD
    cP
    cR
    @52
    @48
    cM
    @13
    @69
    ig1peu.m
    ig1peu.p
    @74
    @59
    ig1peu.d
    @72
    uc1pmon1p
    syl2anc
    elind
    @44
    @29
    @49
    cR
    crlreg
    cfv
    #
    wcel
    @66
    @55
    @58
    @44
    @61
    @75
    @49
    @44
    @29
    @61
    @75
    wss
    @58
    cR
    @61
    @75
    @75
    eqid
    #
    @71
    unitrrg
    syl
    @73
    sseldd
    @68
    @50
    @24
    cD
    cP
    cR
    @52
    @75
    @49
    @13
    ig1peu.d
    ig1peu.p
    @76
    @27
    @74
    @59
    deg1mul3
    syl3anc
    @45
    @55
    vg
    @53
    @11
    @5
    @53
    wceq
    @6
    @54
    @14
    @5
    @53
    cD
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @15
    @45
    @10
    vg
    @11
    @14
    @9
    @6
    eqeq2
    rexbidv
    syl5ibcom
    rexlimdva
    mpd
    @4
    @18
    vg
    vh
    @11
    @11
    @4
    @5
    @11
    wcel
    #
    @13
    @11
    wcel
    #
    wa
    #
    wa
    #
    @16
    @5
    @13
    cP
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @17
    @80
    @16
    @82
    cD
    cfv
    #
    @9
    clt
    wbr
    #
    @83
    @80
    @16
    @85
    @80
    @16
    wa
    cD
    cP
    cR
    @5
    @13
    @81
    cM
    @9
    ig1peu.d
    ig1peu.m
    ig1peu.p
    @81
    eqid
    #
    @4
    @29
    @79
    @16
    @30
    ad2antrr
    @80
    @5
    cM
    wcel
    @16
    @80
    @11
    cM
    @5
    cI
    cM
    inss2
    #
    @4
    @77
    @78
    simprl
    #
    sseldi
    adantr
    @80
    @10
    @15
    simprl
    @80
    @13
    cM
    wcel
    @16
    @80
    @11
    cM
    @13
    @87
    @4
    @77
    @78
    simprr
    #
    sseldi
    adantr
    @80
    @10
    @15
    simprr
    deg1submon1p
    ex
    @80
    @85
    @82
    c.0
    @80
    @82
    c.0
    wne
    #
    @9
    @84
    cle
    wbr
    #
    @85
    wn
    #
    @80
    @90
    @91
    @80
    @90
    wa
    #
    @22
    @84
    @8
    wcel
    #
    @91
    @4
    @22
    @79
    @90
    @31
    ad2antrr
    @93
    @35
    @36
    @82
    @7
    wcel
    #
    @94
    @35
    @93
    @39
    a1i
    @4
    @36
    @79
    @90
    @41
    ad2antrr
    @93
    @82
    cI
    wcel
    #
    @90
    @95
    @80
    @96
    @90
    @80
    @33
    @1
    @5
    cI
    wcel
    @56
    @96
    @4
    @33
    @79
    @34
    adantr
    @0
    @1
    @3
    @79
    simpl2
    @80
    @11
    cI
    @5
    cI
    cM
    inss1
    #
    @88
    sseldi
    @80
    @11
    cI
    @13
    @97
    @89
    sseldi
    cP
    cU
    cI
    @81
    @5
    @13
    ig1peu.u
    @86
    lidlsubcl
    syl22anc
    adantr
    @80
    @90
    simpr
    @82
    cI
    c.0
    eldifsn
    sylanbrc
    @24
    @7
    cD
    @82
    fnfvima
    syl3anc
    @84
    @8
    cc0
    infssuzle
    syl2anc
    ex
    @80
    @9
    cxr
    wcel
    #
    @84
    cxr
    wcel
    #
    @91
    @92
    wb
    @4
    @98
    @79
    @4
    @8
    cxr
    @9
    @8
    cD
    crn
    #
    cxr
    cD
    @7
    imassrn
    @37
    @100
    cxr
    wss
    @38
    @24
    cxr
    cD
    frn
    ax-mp
    sstri
    @42
    sseldi
    adantr
    @80
    @82
    @24
    wcel
    #
    @99
    @80
    cP
    cgrp
    wcel
    #
    @5
    @24
    wcel
    #
    @66
    @101
    @4
    @102
    @79
    @4
    @33
    @102
    @34
    cP
    ringgrp
    syl
    adantr
    #
    @80
    @11
    @24
    @5
    @4
    @11
    @24
    wss
    @79
    @4
    @11
    cI
    @24
    @97
    @28
    syl5ss
    adantr
    #
    @88
    sseldd
    #
    @80
    @11
    @24
    @13
    @105
    @89
    sseldd
    #
    @24
    cP
    @81
    @5
    @13
    @27
    @86
    grpsubcl
    syl3anc
    @24
    cD
    cP
    cR
    @82
    ig1peu.d
    ig1peu.p
    @27
    deg1xrcl
    syl
    @9
    @84
    xrlenlt
    syl2anc
    sylibd
    necon4ad
    syld
    @80
    @102
    @103
    @66
    @83
    @17
    wb
    @104
    @106
    @107
    @24
    cP
    @81
    @5
    @13
    c.0
    @27
    ig1peu.z
    @86
    grpsubeq0
    syl3anc
    sylibd
    ralrimivva
    @10
    @15
    vg
    vh
    @11
    @17
    @6
    @14
    @9
    @5
    @13
    cD
    fveq2
    eqeq1d
    reu4
    sylanbrc
end
