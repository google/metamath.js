include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "cpr.mm"
include "cun.mm"
include "wss.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "icc0.mm"
include "syl2an.mm"
include "biimpar.mm"
include "fveq2d.mm"
include "ctop.mm"
include "retop.mm"
include "ntr0.mm"
include "ax-mp.mm"
include "0ss.mm"
include "eqsstri.mm"
include "syl6eqss.mm"
include "cle.mm"
include "iccssre.mm"
include "uniretop.mm"
include "ntrss2.mm"
include "sylancr.mm"
include "adantr.mm"
include "anim12i.mm"
include "w3a.mm"
include "uncom.mm"
include "prunioo.mm"
include "syl5eq.mm"
include "3expa.mm"
include "sylan.mm"
include "sseqtr4d.mm"
include "simpr.mm"
include "simpl.mm"
include "ltlecasei.mm"
include "cin.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "crp.mm"
include "wrex.mm"
include "ntropn.mm"
include "cxmt.mm"
include "eqid.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "c2.mm"
include "cdiv.mm"
include "ad2antrr.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "ltsubrpd.mm"
include "rpred.mm"
include "resubcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "caddc.mm"
include "rpre.mm"
include "rphalflt.mm"
include "ltsub2dd.mm"
include "readdcld.mm"
include "ltaddrp.mm"
include "sylancom.mm"
include "lttrd.mm"
include "rexrd.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "bl2ioo.mm"
include "eleqtrrd.mm"
include "ssel.mm"
include "syl5com.mm"
include "sseld.mm"
include "wi.mm"
include "elicc2.mm"
include "simp2.mm"
include "syl6bi.mm"
include "3syld.mm"
include "mtod.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "ltaddrpd.mm"
include "ltsubrp.mm"
include "ltadd2dd.mm"
include "simp3.mm"
include "eleq1.mm"
include "notbid.mm"
include "ralprg.mm"
include "mpbir2and.mm"
include "disjr.mm"
include "sylibr.mm"
include "disjssun.mm"
include "syl.mm"
include "iooretop.mm"
include "ioossicc.mm"
include "ssntr.mm"
include "mpanr12.mm"
include "eqssd.mm"

theorem iccntr
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( int ` ( topGen ` ran (,) ) ) ` ( A [,] B ) ) = ( A (,) B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cicc
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    #
    cfv
    #
    cA
    cB
    cioo
    co
    #
    @2
    @6
    cA
    cB
    cpr
    #
    @7
    cun
    #
    wss
    #
    @6
    @7
    wss
    #
    @2
    @10
    cB
    cA
    @2
    cB
    cA
    clt
    wbr
    #
    wa
    #
    @6
    c0
    @5
    cfv
    #
    @9
    @13
    @3
    c0
    @5
    @2
    @3
    c0
    wceq
    #
    @12
    @0
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @15
    @12
    wb
    @1
    cA
    rexr
    #
    cB
    rexr
    #
    cA
    cB
    icc0
    syl2an
    biimpar
    fveq2d
    @14
    c0
    @9
    @4
    ctop
    wcel
    #
    @14
    c0
    wceq
    retop
    @4
    ntr0
    ax-mp
    @9
    0ss
    eqsstri
    syl6eqss
    @2
    cA
    cB
    cle
    wbr
    #
    wa
    @6
    @3
    @9
    @2
    @6
    @3
    wss
    #
    @21
    @2
    @20
    @3
    cr
    wss
    #
    @22
    retop
    cA
    cB
    iccssre
    #
    @3
    @4
    cr
    uniretop
    ntrss2
    sylancr
    #
    adantr
    @2
    @16
    @17
    wa
    @21
    @9
    @3
    wceq
    #
    @0
    @16
    @1
    @17
    @18
    @19
    anim12i
    @16
    @17
    @21
    @26
    @16
    @17
    @21
    w3a
    @9
    @7
    @8
    cun
    @3
    @8
    @7
    uncom
    cA
    cB
    prunioo
    syl5eq
    3expa
    sylan
    sseqtr4d
    @0
    @1
    simpr
    #
    @0
    @1
    simpl
    #
    ltlecasei
    @2
    @6
    @8
    cin
    c0
    wceq
    #
    @10
    @11
    wb
    @2
    vx
    cv
    #
    @6
    wcel
    #
    wn
    #
    vx
    @8
    wral
    #
    @29
    @2
    @33
    cA
    @6
    wcel
    #
    wn
    #
    cB
    @6
    wcel
    #
    wn
    #
    @2
    @34
    cA
    @30
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    #
    co
    #
    @6
    wss
    #
    vx
    crp
    wrex
    #
    @2
    @6
    @4
    wcel
    #
    @34
    @42
    @2
    @20
    @23
    @43
    retop
    @24
    @3
    @4
    cr
    uniretop
    ntropn
    sylancr
    #
    @38
    cr
    cxmt
    cfv
    wcel
    #
    @43
    @34
    @42
    @38
    @38
    eqid
    #
    rexmet
    #
    vx
    @6
    @38
    cA
    @4
    cr
    @38
    @38
    cmopn
    cfv
    #
    @46
    @48
    eqid
    tgioo
    #
    mopni2
    mp3an1
    sylan
    @2
    @34
    wa
    #
    @41
    vx
    crp
    @50
    @30
    crp
    wcel
    #
    wa
    #
    @41
    cA
    cA
    @30
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cle
    wbr
    #
    @52
    @54
    cA
    clt
    wbr
    @55
    wn
    @52
    cA
    @53
    @2
    @0
    @34
    @51
    @28
    ad2antrr
    #
    @51
    @53
    crp
    wcel
    #
    @50
    @30
    rphalfcl
    #
    adantl
    #
    ltsubrpd
    #
    @52
    @54
    cA
    @52
    cA
    @53
    @56
    @52
    @53
    @59
    rpred
    #
    resubcld
    #
    @56
    ltnled
    mpbid
    @52
    @41
    @54
    @6
    wcel
    #
    @54
    @3
    wcel
    #
    @55
    @52
    @54
    @40
    wcel
    @41
    @63
    @52
    @54
    cA
    @30
    cmin
    co
    #
    cA
    @30
    caddc
    co
    #
    cioo
    co
    #
    @40
    @52
    @54
    @67
    wcel
    #
    @54
    cr
    wcel
    #
    @65
    @54
    clt
    wbr
    #
    @54
    @66
    clt
    wbr
    #
    @62
    @52
    @53
    @30
    cA
    @61
    @51
    @30
    cr
    wcel
    #
    @50
    @30
    rpre
    #
    adantl
    #
    @56
    @51
    @53
    @30
    clt
    wbr
    #
    @50
    @30
    rphalflt
    #
    adantl
    ltsub2dd
    @52
    @54
    cA
    @66
    @62
    @56
    @52
    cA
    @30
    @56
    @74
    readdcld
    #
    @60
    @50
    @51
    @0
    cA
    @66
    clt
    wbr
    @56
    cA
    @30
    ltaddrp
    sylancom
    lttrd
    @52
    @65
    cxr
    wcel
    @66
    cxr
    wcel
    @68
    @69
    @70
    @71
    w3a
    wb
    @52
    @65
    @52
    cA
    @30
    @56
    @74
    resubcld
    rexrd
    @52
    @66
    @77
    rexrd
    @65
    @66
    @54
    elioo2
    syl2anc
    mpbir3and
    @52
    @0
    @72
    @40
    @67
    wceq
    @56
    @74
    cA
    @30
    @38
    @46
    bl2ioo
    syl2anc
    eleqtrrd
    @40
    @6
    @54
    ssel
    syl5com
    @52
    @6
    @3
    @54
    @2
    @22
    @34
    @51
    @25
    ad2antrr
    sseld
    @2
    @64
    @55
    wi
    @34
    @51
    @2
    @64
    @69
    @55
    @54
    cB
    cle
    wbr
    #
    w3a
    @55
    cA
    cB
    @54
    elicc2
    @69
    @55
    @78
    simp2
    syl6bi
    ad2antrr
    3syld
    mtod
    nrexdv
    pm2.65da
    @2
    @36
    cB
    @30
    @39
    co
    #
    @6
    wss
    #
    vx
    crp
    wrex
    #
    @2
    @43
    @36
    @81
    @44
    @45
    @43
    @36
    @81
    @47
    vx
    @6
    @38
    cB
    @4
    cr
    @49
    mopni2
    mp3an1
    sylan
    @2
    @36
    wa
    #
    @80
    vx
    crp
    @82
    @51
    wa
    #
    @80
    cB
    @53
    caddc
    co
    #
    cB
    cle
    wbr
    #
    @83
    cB
    @84
    clt
    wbr
    @85
    wn
    @83
    cB
    @53
    @2
    @1
    @36
    @51
    @27
    ad2antrr
    #
    @51
    @57
    @82
    @58
    adantl
    #
    ltaddrpd
    #
    @83
    cB
    @84
    @86
    @83
    cB
    @53
    @86
    @83
    @53
    @87
    rpred
    #
    readdcld
    #
    ltnled
    mpbid
    @83
    @80
    @84
    @6
    wcel
    #
    @84
    @3
    wcel
    #
    @85
    @83
    @84
    @79
    wcel
    @80
    @91
    @83
    @84
    cB
    @30
    cmin
    co
    #
    cB
    @30
    caddc
    co
    #
    cioo
    co
    #
    @79
    @83
    @84
    @95
    wcel
    #
    @84
    cr
    wcel
    #
    @93
    @84
    clt
    wbr
    #
    @84
    @94
    clt
    wbr
    #
    @90
    @83
    @93
    cB
    @84
    @83
    cB
    @30
    @86
    @51
    @72
    @82
    @73
    adantl
    #
    resubcld
    #
    @86
    @90
    @82
    @51
    @1
    @93
    cB
    clt
    wbr
    @86
    cB
    @30
    ltsubrp
    sylancom
    @88
    lttrd
    @83
    @53
    @30
    cB
    @89
    @100
    @86
    @51
    @75
    @82
    @76
    adantl
    ltadd2dd
    @83
    @93
    cxr
    wcel
    @94
    cxr
    wcel
    @96
    @97
    @98
    @99
    w3a
    wb
    @83
    @93
    @101
    rexrd
    @83
    @94
    @83
    cB
    @30
    @86
    @100
    readdcld
    rexrd
    @93
    @94
    @84
    elioo2
    syl2anc
    mpbir3and
    @83
    @1
    @72
    @79
    @95
    wceq
    @86
    @100
    cB
    @30
    @38
    @46
    bl2ioo
    syl2anc
    eleqtrrd
    @79
    @6
    @84
    ssel
    syl5com
    @83
    @6
    @3
    @84
    @2
    @22
    @36
    @51
    @25
    ad2antrr
    sseld
    @2
    @92
    @85
    wi
    @36
    @51
    @2
    @92
    @97
    cA
    @84
    cle
    wbr
    #
    @85
    w3a
    @85
    cA
    cB
    @84
    elicc2
    @97
    @102
    @85
    simp3
    syl6bi
    ad2antrr
    3syld
    mtod
    nrexdv
    pm2.65da
    @32
    @35
    @37
    vx
    cA
    cB
    cr
    cr
    @30
    cA
    wceq
    @31
    @34
    @30
    cA
    @6
    eleq1
    notbid
    @30
    cB
    wceq
    @31
    @36
    @30
    cB
    @6
    eleq1
    notbid
    ralprg
    mpbir2and
    vx
    @6
    @8
    disjr
    sylibr
    @6
    @8
    @7
    disjssun
    syl
    mpbid
    @2
    @20
    @23
    @7
    @6
    wss
    #
    retop
    @24
    @20
    @23
    wa
    @7
    @4
    wcel
    @7
    @3
    wss
    @103
    cA
    cB
    iooretop
    cA
    cB
    ioossicc
    @3
    @4
    @7
    cr
    uniretop
    ssntr
    mpanr12
    sylancr
    eqssd
end
