include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "wcel.mm"
include "wn.mm"
include "cn.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "ccnv.mm"
include "cres.mm"
include "wfun.mm"
include "w3a.mm"
include "wex.mm"
include "brdom2.mm"
include "wi.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wa.mm"
include "cfn.mm"
include "isfinite2.mm"
include "isfinite4.mm"
include "sylib.mm"
include "adantr.mm"
include "bren.mm"
include "3adant3.mm"
include "nfv.mm"
include "cdif.mm"
include "cmpt.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "f1of.mm"
include "adantl.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "eqcomi.mm"
include "wb.mm"
include "simplr.mm"
include "fconst2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "disjdif.mm"
include "a1i.mm"
include "fun.mm"
include "syl21anc.mm"
include "fz1ssnn.mm"
include "undif.mm"
include "mpbi.mm"
include "feq2i.mm"
include "3adantl3.mm"
include "ssid.mm"
include "wfo.mm"
include "simpr.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5sseqr.mm"
include "orcd.mm"
include "ssun.mm"
include "rnun.mm"
include "syl6sseqr.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "cnvun.mm"
include "reseq1i.mm"
include "resundir.mm"
include "eqtri.mm"
include "wfn.mm"
include "dff1o4.mm"
include "fnresdm.mm"
include "simpl3.mm"
include "cnveqi.mm"
include "cnvxp.mm"
include "incom.mm"
include "disjsn.mm"
include "biimpri.mm"
include "syl5eqr.mm"
include "xpdisjres.mm"
include "syl5eq.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"
include "funeqd.mm"
include "mpbird.mm"
include "vex.mm"
include "cvv.mm"
include "nnex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "mptex.mm"
include "unex.mm"
include "feq1.mm"
include "rneq.mm"
include "sseq2d.mm"
include "cnveq.mm"
include "eqidd.mm"
include "reseq12d.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "syl3anc.mm"
include "ex.mm"
include "exlimd.mm"
include "mpd.mm"
include "3expia.mm"
include "nnenom.mm"
include "simpl.mm"
include "ensymd.mm"
include "entr.mm"
include "sylancr.mm"
include "ssun1.mm"
include "fss.mm"
include "mpan2.mm"
include "wf1.mm"
include "cima.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "f1ores.mm"
include "f1ofun.mm"
include "3jca.mm"
include "eximd.mm"
include "a1d.mm"
include "jaoian.mm"
include "3impia.mm"
include "syl3an1b.mm"

theorem padct
  let cA: class A
  let vf: setvar f
  let cV: class V
  let cZ: class Z
  let vg: setvar g
  let vx: setvar x

  disjoint A f
  disjoint V f
  disjoint Z f
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint V g
  disjoint Z g
  disjoint Z x
  assert |- ( ( A ~<_ _om /\ Z e. V /\ -. Z e. A ) -> E. f ( f : NN --> ( A u. { Z } ) /\ A C_ ran f /\ Fun ( `' f |` A ) ) )

  proof
    cA
    com
    cdom
    wbr
    cA
    com
    csdm
    wbr
    #
    cA
    com
    cen
    wbr
    #
    wo
    #
    cZ
    cV
    wcel
    #
    cZ
    cA
    wcel
    wn
    #
    cn
    cA
    cZ
    csn
    #
    cun
    #
    vf
    cv
    #
    wf
    #
    cA
    @7
    crn
    #
    wss
    #
    @7
    ccnv
    #
    cA
    cres
    #
    wfun
    #
    w3a
    #
    vf
    wex
    #
    cA
    com
    brdom2
    @2
    @3
    @4
    @15
    @0
    @3
    @4
    @15
    wi
    @1
    @0
    @3
    @4
    @15
    @0
    @3
    @4
    w3a
    #
    c1
    cA
    chash
    cfv
    #
    cfz
    co
    #
    cA
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    @15
    @0
    @3
    @21
    @4
    @0
    @3
    wa
    #
    @18
    cA
    cen
    wbr
    #
    @21
    @0
    @23
    @3
    @0
    cA
    cfn
    wcel
    @23
    cA
    isfinite2
    cA
    isfinite4
    sylib
    adantr
    @18
    cA
    vg
    bren
    sylib
    3adant3
    @16
    @20
    @15
    vg
    @16
    vg
    nfv
    @15
    vg
    nfv
    @16
    @20
    @15
    @16
    @20
    wa
    #
    cn
    @6
    @19
    vx
    cn
    @18
    cdif
    #
    cZ
    cmpt
    #
    cun
    #
    wf
    #
    cA
    @27
    crn
    #
    wss
    #
    @27
    ccnv
    #
    cA
    cres
    #
    wfun
    #
    @15
    @0
    @3
    @20
    @28
    @4
    @22
    @20
    wa
    #
    @18
    @25
    cun
    #
    @6
    @27
    wf
    #
    @28
    @34
    @18
    cA
    @19
    wf
    #
    @25
    @5
    @26
    wf
    #
    @18
    @25
    cin
    c0
    wceq
    #
    @36
    @20
    @37
    @22
    @18
    cA
    @19
    f1of
    adantl
    @34
    @38
    @26
    @25
    @5
    cxp
    #
    wceq
    #
    @40
    @26
    vx
    @25
    cZ
    fconstmpt
    eqcomi
    #
    @34
    @3
    @38
    @41
    wb
    @0
    @3
    @20
    simplr
    @25
    cZ
    cV
    @26
    fconst2g
    syl
    mpbiri
    @39
    @34
    @18
    cn
    disjdif
    a1i
    @18
    @25
    cA
    @5
    @19
    @26
    fun
    syl21anc
    @35
    cn
    @6
    @27
    @18
    cn
    wss
    @35
    cn
    wceq
    @17
    fz1ssnn
    @18
    cn
    undif
    mpbi
    feq2i
    sylib
    3adantl3
    @0
    @3
    @20
    @30
    @4
    @34
    cA
    @19
    crn
    #
    @26
    crn
    #
    cun
    #
    @29
    @34
    cA
    @43
    wss
    #
    cA
    @44
    wss
    #
    wo
    cA
    @45
    wss
    @34
    @46
    @47
    @34
    cA
    cA
    @43
    cA
    ssid
    #
    @34
    @20
    @18
    cA
    @19
    wfo
    #
    @43
    cA
    wceq
    @22
    @20
    simpr
    @18
    cA
    @19
    f1ofo
    @18
    cA
    @19
    forn
    3syl
    syl5sseqr
    orcd
    cA
    @43
    @44
    ssun
    syl
    @19
    @26
    rnun
    syl6sseqr
    3adantl3
    @24
    @33
    @19
    ccnv
    #
    wfun
    #
    @20
    @51
    @16
    @20
    @49
    @51
    @18
    cA
    @19
    dff1o3
    simprbi
    adantl
    @24
    @32
    @50
    @24
    @32
    @50
    cA
    cres
    #
    @26
    ccnv
    #
    cA
    cres
    #
    cun
    #
    @50
    @32
    @50
    @53
    cun
    #
    cA
    cres
    @55
    @31
    @56
    cA
    @19
    @26
    cnvun
    reseq1i
    @50
    @53
    cA
    resundir
    eqtri
    @24
    @55
    @50
    c0
    cun
    @50
    @24
    @52
    @50
    @54
    c0
    @20
    @52
    @50
    wceq
    #
    @16
    @20
    @50
    cA
    wfn
    #
    @57
    @20
    @19
    @18
    wfn
    @58
    @18
    cA
    @19
    dff1o4
    simprbi
    cA
    @50
    fnresdm
    syl
    adantl
    @24
    @4
    @54
    c0
    wceq
    @0
    @3
    @4
    @20
    simpl3
    @4
    @54
    @5
    @25
    cxp
    #
    cA
    cres
    #
    c0
    @53
    @59
    cA
    @53
    @40
    ccnv
    @59
    @26
    @40
    @42
    cnveqi
    @25
    @5
    cnvxp
    eqtri
    reseq1i
    @4
    @5
    cA
    cin
    #
    c0
    wceq
    @60
    c0
    wceq
    @4
    @61
    cA
    @5
    cin
    #
    c0
    cA
    @5
    incom
    @62
    c0
    wceq
    @4
    cA
    cZ
    disjsn
    biimpri
    syl5eqr
    @5
    @25
    cA
    xpdisjres
    syl
    syl5eq
    syl
    uneq12d
    @50
    un0
    syl6eq
    syl5eq
    funeqd
    mpbird
    @14
    @28
    @30
    @33
    w3a
    vf
    @27
    @19
    @26
    vg
    vex
    vx
    @25
    cZ
    cn
    cvv
    wcel
    @25
    cvv
    wcel
    nnex
    cn
    @18
    cvv
    difexg
    ax-mp
    mptex
    unex
    @7
    @27
    wceq
    #
    @8
    @28
    @10
    @30
    @13
    @33
    cn
    @6
    @7
    @27
    feq1
    @63
    @9
    @29
    cA
    @7
    @27
    rneq
    sseq2d
    @63
    @12
    @32
    @63
    @11
    @31
    cA
    cA
    @7
    @27
    cnveq
    @63
    cA
    eqidd
    reseq12d
    funeqd
    3anbi123d
    spcev
    syl3anc
    ex
    exlimd
    mpd
    3expia
    @1
    @3
    wa
    #
    @15
    @4
    @64
    cn
    cA
    @7
    wf1o
    #
    vf
    wex
    #
    @15
    @64
    cn
    cA
    cen
    wbr
    #
    @66
    @64
    cn
    com
    cen
    wbr
    com
    cA
    cen
    wbr
    @67
    nnenom
    @64
    cA
    com
    @1
    @3
    simpl
    ensymd
    cn
    com
    cA
    entr
    sylancr
    cn
    cA
    vf
    bren
    sylib
    @64
    @65
    @14
    vf
    @64
    vf
    nfv
    @64
    @65
    @14
    @64
    @65
    wa
    #
    @8
    @10
    @13
    @68
    @65
    cn
    cA
    @7
    wf
    #
    @8
    @64
    @65
    simpr
    #
    cn
    cA
    @7
    f1of
    @69
    cA
    @6
    wss
    @8
    cA
    @5
    ssun1
    cn
    cA
    @6
    @7
    fss
    mpan2
    3syl
    @68
    cA
    cA
    @9
    @48
    @68
    @65
    cn
    cA
    @7
    wfo
    @9
    cA
    wceq
    @70
    cn
    cA
    @7
    f1ofo
    cn
    cA
    @7
    forn
    3syl
    syl5sseqr
    @68
    cA
    cn
    @11
    wf1
    #
    cA
    @11
    cA
    cima
    #
    @12
    wf1o
    #
    @13
    @68
    @65
    cA
    cn
    @11
    wf1o
    @71
    @70
    cn
    cA
    @7
    f1ocnv
    cA
    cn
    @11
    f1of1
    3syl
    @71
    cA
    cA
    wss
    @73
    @48
    cA
    cn
    cA
    @11
    f1ores
    mpan2
    cA
    @72
    @12
    f1ofun
    3syl
    3jca
    ex
    eximd
    mpd
    a1d
    jaoian
    3impia
    syl3an1b
end
