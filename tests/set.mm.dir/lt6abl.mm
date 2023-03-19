include "cgrp.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cabl.mm"
include "wa.mm"
include "cuz.mm"
include "cz.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "adantr.mm"
include "cfn.mm"
include "wb.mm"
include "cpnf.mm"
include "cr.mm"
include "cxr.mm"
include "wn.mm"
include "6re.mm"
include "rexr.mm"
include "pnfnlt.mm"
include "mp2b.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "hashinf.mm"
include "sylan.mm"
include "breq1d.mm"
include "biimpd.mm"
include "impancom.mm"
include "mt3i.mm"
include "hashnncl.mm"
include "syl.mm"
include "mpbird.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "6nn.mm"
include "nnzi.mm"
include "simpr.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "c5.mm"
include "wo.mm"
include "caddc.mm"
include "df-6.mm"
include "oveq2i.mm"
include "eleq2i.mm"
include "5nn.mm"
include "eleqtri.mm"
include "fzosplitsni.mm"
include "ax-mp.mm"
include "bitri.mm"
include "c4.mm"
include "df-5.mm"
include "4nn.mm"
include "c3.mm"
include "df-4.mm"
include "3nn.mm"
include "c2.mm"
include "df-3.mm"
include "2eluzge1.mm"
include "c1o.mm"
include "cen.mm"
include "csn.mm"
include "elsni.mm"
include "fzo12sn.mm"
include "eleq2s.mm"
include "adantl.mm"
include "hash1.mm"
include "syl6eqr.mm"
include "cn0.mm"
include "1nn0.mm"
include "syl6eqel.mm"
include "hashclb.mm"
include "sylibr.mm"
include "com.mm"
include "1onn.mm"
include "nnfi.mm"
include "hashen.mm"
include "sylancl.mm"
include "mpbid.mm"
include "ccyg.mm"
include "0cyg.mm"
include "cygabl.mm"
include "syldan.mm"
include "ex.mm"
include "cprime.mm"
include "id.mm"
include "2prm.mm"
include "prmcyg.mm"
include "syl5.mm"
include "jaod.mm"
include "syl5bi.mm"
include "3prm.mm"
include "cv.mm"
include "cod.mm"
include "cdvds.mm"
include "wral.mm"
include "cgex.mm"
include "simpl.mm"
include "2z.mm"
include "eqid.mm"
include "gexdvds2.mm"
include "wi.mm"
include "gex2abl.mm"
include "sylbird.mm"
include "wrex.mm"
include "rexnal.mm"
include "simprl.mm"
include "odcl.mm"
include "ad2antrl.mm"
include "4nn0.mm"
include "oddvds2.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "cpc.mm"
include "cexp.mm"
include "sq2.mm"
include "2nn0.mm"
include "cle.mm"
include "odcl2.mm"
include "pccl.mm"
include "sylancr.mm"
include "nn0zd.mm"
include "df-2.mm"
include "simprr.mm"
include "dvdsexp.mm"
include "3expia.mm"
include "1z.mm"
include "eluz.mm"
include "oveq2.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "rspcev.mm"
include "pcprmpw2.mm"
include "eqcomd.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "breq12d.mm"
include "3imtr3d.mm"
include "mtod.mm"
include "1re.mm"
include "nn0red.mm"
include "ltnle.mm"
include "nn0ltp1le.mm"
include "syl5eqbr.mm"
include "eluz2.mm"
include "syl5eqbrr.mm"
include "breqtrrd.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "eqtr4d.mm"
include "iscygodd.mm"
include "rexlimdvaa.mm"
include "syl5bir.mm"
include "pm2.61d.mm"
include "5prm.mm"
include "imp.mm"

theorem lt6abl
  let cB: class B
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )


  assert |- ( ( G e. Grp /\ ( # ` B ) < 6 ) -> G e. Abel )

  proof
    cG
    cgrp
    wcel
    #
    cB
    chash
    cfv
    #
    c6
    clt
    wbr
    #
    @1
    c1
    c6
    cfzo
    co
    #
    wcel
    #
    cG
    cabl
    wcel
    #
    @0
    @2
    wa
    #
    @1
    c1
    cuz
    cfv
    #
    wcel
    c6
    cz
    wcel
    #
    @2
    @4
    @6
    @1
    cn
    @7
    @6
    @1
    cn
    wcel
    #
    cB
    c0
    wne
    #
    @0
    @10
    @2
    cB
    cG
    cygctb.1
    grpbn0
    adantr
    @6
    cB
    cfn
    wcel
    #
    @9
    @10
    wb
    @6
    @11
    cpnf
    c6
    clt
    wbr
    #
    c6
    cr
    wcel
    c6
    cxr
    wcel
    @12
    wn
    6re
    c6
    rexr
    c6
    pnfnlt
    mp2b
    @0
    @11
    wn
    #
    @2
    @12
    @0
    @13
    wa
    #
    @2
    @12
    @14
    @1
    cpnf
    c6
    clt
    @0
    cB
    cvv
    wcel
    #
    @13
    @1
    cpnf
    wceq
    @15
    @0
    cB
    cG
    cbs
    cfv
    cvv
    cygctb.1
    cG
    cbs
    fvex
    eqeltri
    #
    a1i
    cB
    cvv
    hashinf
    sylan
    breq1d
    biimpd
    impancom
    mt3i
    cB
    hashnncl
    syl
    mpbird
    nnuz
    syl6eleq
    @8
    @6
    c6
    6nn
    nnzi
    a1i
    @0
    @2
    simpr
    @1
    c1
    c6
    elfzo2
    syl3anbrc
    @0
    @4
    @5
    @4
    @1
    c1
    c5
    cfzo
    co
    #
    wcel
    #
    @1
    c5
    wceq
    #
    wo
    #
    @0
    @5
    @4
    @1
    c1
    c5
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @20
    @3
    @22
    @1
    c6
    @21
    c1
    cfzo
    df-6
    oveq2i
    eleq2i
    c5
    @7
    wcel
    @23
    @20
    wb
    c5
    cn
    @7
    5nn
    nnuz
    eleqtri
    c1
    c5
    @1
    fzosplitsni
    ax-mp
    bitri
    @0
    @18
    @5
    @19
    @18
    @1
    c1
    c4
    cfzo
    co
    #
    wcel
    #
    @1
    c4
    wceq
    #
    wo
    #
    @0
    @5
    @18
    @1
    c1
    c4
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @27
    @17
    @29
    @1
    c5
    @28
    c1
    cfzo
    df-5
    oveq2i
    eleq2i
    c4
    @7
    wcel
    @30
    @27
    wb
    c4
    cn
    @7
    4nn
    nnuz
    eleqtri
    c1
    c4
    @1
    fzosplitsni
    ax-mp
    bitri
    @0
    @25
    @5
    @26
    @25
    @1
    c1
    c3
    cfzo
    co
    #
    wcel
    #
    @1
    c3
    wceq
    #
    wo
    #
    @0
    @5
    @25
    @1
    c1
    c3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @34
    @24
    @36
    @1
    c4
    @35
    c1
    cfzo
    df-4
    oveq2i
    eleq2i
    c3
    @7
    wcel
    @37
    @34
    wb
    c3
    cn
    @7
    3nn
    nnuz
    eleqtri
    c1
    c3
    @1
    fzosplitsni
    ax-mp
    bitri
    @0
    @32
    @5
    @33
    @32
    @1
    c1
    c2
    cfzo
    co
    #
    wcel
    #
    @1
    c2
    wceq
    #
    wo
    #
    @0
    @5
    @32
    @1
    c1
    c2
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @41
    @31
    @43
    @1
    c3
    @42
    c1
    cfzo
    df-3
    oveq2i
    eleq2i
    c2
    @7
    wcel
    @44
    @41
    wb
    2eluzge1
    c1
    c2
    @1
    fzosplitsni
    ax-mp
    bitri
    @0
    @39
    @5
    @40
    @0
    @39
    @5
    @0
    @39
    cB
    c1o
    cen
    wbr
    #
    @5
    @0
    @39
    wa
    #
    @1
    c1o
    chash
    cfv
    #
    wceq
    #
    @45
    @46
    @1
    c1
    @47
    @39
    @1
    c1
    wceq
    #
    @0
    @49
    @1
    c1
    csn
    @38
    @1
    c1
    elsni
    fzo12sn
    eleq2s
    adantl
    #
    hash1
    syl6eqr
    @46
    @11
    c1o
    cfn
    wcel
    #
    @48
    @45
    wb
    @46
    @1
    cn0
    wcel
    #
    @11
    @46
    @1
    c1
    cn0
    @50
    1nn0
    syl6eqel
    @15
    @11
    @52
    wb
    @16
    cB
    cvv
    hashclb
    ax-mp
    #
    sylibr
    c1o
    com
    wcel
    @51
    1onn
    c1o
    nnfi
    ax-mp
    cB
    c1o
    hashen
    sylancl
    mpbid
    @0
    @45
    wa
    cG
    ccyg
    wcel
    #
    @5
    cB
    cG
    cygctb.1
    0cyg
    cG
    cygabl
    #
    syl
    syldan
    ex
    @40
    @1
    cprime
    wcel
    #
    @0
    @5
    @40
    @1
    c2
    cprime
    @40
    id
    2prm
    syl6eqel
    @0
    @56
    @5
    @0
    @56
    wa
    @54
    @5
    cB
    cG
    cygctb.1
    prmcyg
    @55
    syl
    ex
    #
    syl5
    jaod
    syl5bi
    @33
    @56
    @0
    @5
    @33
    @1
    c3
    cprime
    @33
    id
    3prm
    syl6eqel
    @57
    syl5
    jaod
    syl5bi
    @0
    @26
    @5
    @0
    @26
    wa
    #
    vx
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    #
    c2
    cdvds
    wbr
    #
    vx
    cB
    wral
    #
    @5
    @58
    @63
    cG
    cgex
    cfv
    #
    c2
    cdvds
    wbr
    #
    @5
    @58
    @0
    c2
    cz
    wcel
    #
    @65
    @63
    wb
    @0
    @26
    simpl
    #
    2z
    vx
    @64
    cG
    c2
    @60
    cB
    cygctb.1
    @64
    eqid
    #
    @60
    eqid
    #
    gexdvds2
    sylancl
    @0
    @65
    @5
    wi
    @26
    @0
    @65
    @5
    @64
    cG
    cB
    cygctb.1
    @68
    gex2abl
    ex
    adantr
    sylbird
    @63
    wn
    @62
    wn
    #
    vx
    cB
    wrex
    @58
    @5
    @62
    vx
    cB
    rexnal
    @58
    @70
    @5
    vx
    cB
    @58
    @59
    cB
    wcel
    #
    @70
    wa
    #
    wa
    #
    @54
    @5
    @73
    cB
    cG
    @60
    @59
    cygctb.1
    @69
    @58
    @0
    @72
    @67
    adantr
    #
    @58
    @71
    @70
    simprl
    #
    @73
    @61
    c4
    @1
    @73
    @61
    cn0
    wcel
    #
    c4
    cn0
    wcel
    #
    @61
    c4
    cdvds
    wbr
    #
    c4
    @61
    cdvds
    wbr
    @61
    c4
    wceq
    @71
    @76
    @58
    @70
    @59
    cG
    @60
    cB
    cygctb.1
    @69
    odcl
    ad2antrl
    @77
    @73
    4nn0
    a1i
    @73
    @61
    @1
    c4
    cdvds
    @73
    @0
    @11
    @71
    @61
    @1
    cdvds
    wbr
    @74
    @58
    @11
    @72
    @58
    @52
    @11
    @58
    @1
    c4
    cn0
    @0
    @26
    simpr
    #
    4nn0
    syl6eqel
    @53
    sylibr
    adantr
    #
    @75
    @59
    cG
    @60
    cB
    cygctb.1
    @69
    oddvds2
    syl3anc
    @58
    @26
    @72
    @79
    adantr
    #
    breqtrd
    #
    @73
    c4
    c2
    c2
    @61
    cpc
    co
    #
    cexp
    co
    #
    @61
    cdvds
    @73
    c4
    c2
    c2
    cexp
    co
    #
    @84
    cdvds
    sq2
    @73
    @66
    c2
    cn0
    wcel
    #
    @83
    c2
    cuz
    cfv
    wcel
    #
    @85
    @84
    cdvds
    wbr
    @66
    @73
    2z
    a1i
    #
    @86
    @73
    2nn0
    a1i
    @73
    @66
    @83
    cz
    wcel
    #
    c2
    @83
    cle
    wbr
    @87
    @88
    @73
    @83
    @73
    c2
    cprime
    wcel
    #
    @61
    cn
    wcel
    #
    @83
    cn0
    wcel
    #
    2prm
    @73
    @0
    @11
    @71
    @91
    @74
    @80
    @75
    @59
    cG
    @60
    cB
    cygctb.1
    @69
    odcl2
    syl3anc
    #
    c2
    @61
    pccl
    sylancr
    #
    nn0zd
    #
    @73
    c2
    c1
    c1
    caddc
    co
    #
    @83
    cle
    df-2
    @73
    c1
    @83
    clt
    wbr
    #
    @96
    @83
    cle
    wbr
    #
    @73
    @97
    @83
    c1
    cle
    wbr
    #
    wn
    #
    @73
    @99
    @62
    @58
    @71
    @70
    simprr
    @73
    c1
    @83
    cuz
    cfv
    wcel
    #
    @84
    c2
    c1
    cexp
    co
    #
    cdvds
    wbr
    #
    @99
    @62
    @73
    @66
    @92
    @101
    @103
    wi
    2z
    @94
    @66
    @92
    @101
    @103
    c2
    @83
    c1
    dvdsexp
    3expia
    sylancr
    @73
    @89
    c1
    cz
    wcel
    @101
    @99
    wb
    @95
    1z
    @83
    c1
    eluz
    sylancl
    @73
    @84
    @61
    @102
    c2
    cdvds
    @73
    @61
    @84
    @73
    @61
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @61
    @84
    wceq
    #
    @73
    @86
    @78
    @107
    2nn0
    @82
    @106
    @78
    vn
    c2
    cn0
    @104
    c2
    wceq
    #
    @105
    c4
    @61
    cdvds
    @109
    @105
    @85
    c4
    @104
    c2
    c2
    cexp
    oveq2
    sq2
    syl6eq
    breq2d
    rspcev
    sylancr
    @73
    @90
    @91
    @107
    @108
    wb
    2prm
    @93
    @61
    c2
    vn
    pcprmpw2
    sylancr
    mpbid
    #
    eqcomd
    @102
    c2
    wceq
    #
    @73
    c2
    cc
    wcel
    @111
    2cn
    c2
    exp1
    ax-mp
    a1i
    breq12d
    3imtr3d
    mtod
    @73
    c1
    cr
    wcel
    @83
    cr
    wcel
    @97
    @100
    wb
    1re
    @73
    @83
    @94
    nn0red
    c1
    @83
    ltnle
    sylancr
    mpbird
    @73
    c1
    cn0
    wcel
    @92
    @97
    @98
    wb
    1nn0
    @94
    c1
    @83
    nn0ltp1le
    sylancr
    mpbid
    syl5eqbr
    c2
    @83
    eluz2
    syl3anbrc
    c2
    c2
    @83
    dvdsexp
    syl3anc
    syl5eqbrr
    @110
    breqtrrd
    @61
    c4
    dvdseq
    syl22anc
    @81
    eqtr4d
    iscygodd
    @55
    syl
    rexlimdvaa
    syl5bir
    pm2.61d
    ex
    jaod
    syl5bi
    @19
    @56
    @0
    @5
    @19
    @1
    c5
    cprime
    @19
    id
    5prm
    syl6eqel
    @57
    syl5
    jaod
    syl5bi
    imp
    syldan
end
