include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cprime.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cfz.mm"
include "wral.mm"
include "clt.mm"
include "simpl.mm"
include "caddc.mm"
include "2nn0.mm"
include "numexp1.mm"
include "df-2.mm"
include "eqtri.mm"
include "prmuz2.mm"
include "adantl.mm"
include "cn.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "syl.mm"
include "1red.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "reexpclzd.mm"
include "ltaddsubd.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "1zzd.mm"
include "1lt2.mm"
include "ltexp2d.mm"
include "eluz2b1.mm"
include "sylanbrc.mm"
include "cdiv.mm"
include "cmul.mm"
include "simpllr.mm"
include "prmnn.mm"
include "nncnd.mm"
include "cn0.mm"
include "2nn.mm"
include "elfzuz.mm"
include "ad2antlr.mm"
include "eluz2nn.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "zred.mm"
include "recnd.mm"
include "0red.mm"
include "0lt1.mm"
include "elfzelz.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "nnred.mm"
include "lttrd.mm"
include "elnnz.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "eqeltrd.mm"
include "csu.mm"
include "cneg.mm"
include "cc.mm"
include "wceq.mm"
include "wb.mm"
include "ax-1cn.mm"
include "subeq0.mm"
include "sylancl.mm"
include "necon3bid.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "nndivdvds.mm"
include "syl2anc.mm"
include "geoser.mm"
include "negsubdi2.mm"
include "oveq2d.mm"
include "expmuld.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "div2negd.mm"
include "3eqtr2d.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "zexpcl.mm"
include "syl2an.mm"
include "fsumzcl.mm"
include "eqeltrrd.mm"
include "mulid2d.mm"
include "cle.mm"
include "w3a.mm"
include "2z.mm"
include "elfzm11.mm"
include "biimpa.mm"
include "simp3d.mm"
include "adantr.mm"
include "ltsub1dd.mm"
include "eqbrtrd.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "nprm.mm"
include "pm2.65da.mm"
include "ralrimiva.mm"
include "isprm3.mm"

theorem mersenne
  let cP: class P
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( P e. ZZ /\ ( ( 2 ^ P ) - 1 ) e. Prime ) -> P e. Prime )

  proof
    cP
    cz
    wcel
    #
    c2
    cP
    cexp
    co
    #
    c1
    cmin
    co
    #
    cprime
    wcel
    #
    wa
    #
    cP
    c2
    cuz
    cfv
    #
    wcel
    #
    vk
    cv
    #
    cP
    cdvds
    wbr
    #
    wn
    #
    vk
    c2
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    cP
    cprime
    wcel
    @4
    @0
    c1
    cP
    clt
    wbr
    #
    @6
    @0
    @3
    simpl
    #
    @4
    @12
    c2
    c1
    cexp
    co
    #
    @1
    clt
    wbr
    @4
    @14
    c1
    c1
    caddc
    co
    #
    @1
    clt
    @14
    c2
    @15
    c2
    2nn0
    numexp1
    df-2
    eqtri
    #
    @4
    @15
    @1
    clt
    wbr
    c1
    @2
    clt
    wbr
    #
    @4
    @2
    @5
    wcel
    #
    @17
    @3
    @18
    @0
    @2
    prmuz2
    adantl
    @18
    @2
    cn
    wcel
    #
    @17
    @2
    eluz2b2
    simprbi
    syl
    @4
    c1
    c1
    @1
    @4
    1red
    #
    @20
    @4
    c2
    cP
    c2
    cr
    wcel
    #
    @4
    2re
    a1i
    #
    c2
    cc0
    wne
    @4
    2ne0
    a1i
    @13
    reexpclzd
    #
    ltaddsubd
    mpbird
    syl5eqbr
    @4
    c2
    c1
    cP
    @22
    @4
    1zzd
    @13
    c1
    c2
    clt
    wbr
    #
    @4
    1lt2
    a1i
    ltexp2d
    mpbird
    cP
    eluz2b1
    sylanbrc
    #
    @4
    @9
    vk
    @11
    @4
    @7
    @11
    wcel
    #
    wa
    #
    @8
    c2
    @7
    cexp
    co
    #
    c1
    cmin
    co
    #
    @2
    @29
    cdiv
    co
    #
    cmul
    co
    #
    cprime
    wcel
    #
    @27
    @8
    wa
    #
    @31
    @2
    cprime
    @33
    @2
    @29
    @33
    @2
    @33
    @3
    @19
    @0
    @3
    @26
    @8
    simpllr
    #
    @2
    prmnn
    syl
    #
    nncnd
    #
    @33
    @29
    @33
    @29
    @33
    @28
    cz
    wcel
    #
    @29
    cz
    wcel
    #
    @33
    @28
    @33
    c2
    cn
    wcel
    @7
    cn0
    wcel
    @28
    cn
    wcel
    2nn
    @33
    @7
    @33
    @7
    @5
    wcel
    #
    @7
    cn
    wcel
    #
    @26
    @39
    @4
    @8
    @7
    c2
    @10
    elfzuz
    ad2antlr
    #
    @7
    eluz2nn
    syl
    #
    nnnn0d
    #
    c2
    @7
    nnexpcl
    sylancr
    #
    nnzd
    #
    @28
    peano2zm
    syl
    #
    zred
    #
    recnd
    #
    @33
    @29
    @33
    @38
    cc0
    @29
    clt
    wbr
    #
    @29
    cn
    wcel
    #
    @46
    @33
    cc0
    c1
    @29
    @33
    0red
    @33
    1red
    #
    @47
    cc0
    c1
    clt
    wbr
    @33
    0lt1
    a1i
    @33
    @15
    @28
    clt
    wbr
    c1
    @29
    clt
    wbr
    #
    @33
    @15
    @14
    @28
    clt
    @16
    @33
    c1
    @7
    clt
    wbr
    #
    @14
    @28
    clt
    wbr
    @33
    @39
    @53
    @41
    @39
    @40
    @53
    @7
    eluz2b2
    simprbi
    syl
    @33
    c2
    c1
    @7
    @21
    @33
    2re
    a1i
    #
    @33
    1zzd
    @26
    @7
    cz
    wcel
    #
    @4
    @8
    @7
    c2
    @10
    elfzelz
    ad2antlr
    #
    @24
    @33
    1lt2
    a1i
    #
    ltexp2d
    mpbid
    syl5eqbrr
    @33
    c1
    c1
    @28
    @51
    @51
    @33
    @28
    @44
    nnred
    #
    ltaddsubd
    mpbid
    #
    lttrd
    #
    @29
    elnnz
    sylanbrc
    #
    nnne0d
    #
    divcan2d
    @34
    eqeltrd
    @33
    @29
    @5
    wcel
    #
    @30
    @5
    wcel
    #
    @32
    wn
    @33
    @50
    @52
    @63
    @61
    @59
    @29
    eluz2b2
    sylanbrc
    @33
    @30
    cz
    wcel
    c1
    @30
    clt
    wbr
    #
    @64
    @33
    cc0
    cP
    @7
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    @28
    vn
    cv
    #
    cexp
    co
    #
    vn
    csu
    #
    @30
    cz
    @33
    @71
    c1
    @28
    @66
    cexp
    co
    #
    cmin
    co
    #
    c1
    @28
    cmin
    co
    #
    cdiv
    co
    @2
    cneg
    #
    @29
    cneg
    #
    cdiv
    co
    @30
    @33
    @28
    vn
    @66
    @33
    @28
    @44
    nncnd
    #
    @33
    @29
    cc0
    wne
    @28
    c1
    wne
    @62
    @33
    @29
    cc0
    @28
    c1
    @33
    @28
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @29
    cc0
    wceq
    @28
    c1
    wceq
    wb
    @77
    ax-1cn
    @28
    c1
    subeq0
    sylancl
    necon3bid
    mpbid
    @33
    @66
    @33
    @8
    @66
    cn
    wcel
    #
    @27
    @8
    simpr
    @33
    cP
    cn
    wcel
    #
    @40
    @8
    @80
    wb
    @4
    @81
    @26
    @8
    @4
    @6
    @81
    @25
    cP
    eluz2nn
    syl
    ad2antrr
    #
    @42
    cP
    @7
    nndivdvds
    syl2anc
    mpbid
    nnnn0d
    #
    geoser
    @33
    @75
    @73
    @76
    @74
    cdiv
    @33
    @75
    c1
    @1
    cmin
    co
    #
    @73
    @33
    @1
    cc
    wcel
    @79
    @75
    @84
    wceq
    @33
    @1
    @4
    @1
    cr
    wcel
    @26
    @8
    @23
    ad2antrr
    #
    recnd
    ax-1cn
    @1
    c1
    negsubdi2
    sylancl
    @33
    @1
    @72
    c1
    cmin
    @33
    c2
    @7
    @66
    cmul
    co
    #
    cexp
    co
    @1
    @72
    @33
    @86
    cP
    c2
    cexp
    @33
    cP
    @7
    @33
    cP
    @82
    nncnd
    @33
    @7
    @42
    nncnd
    @33
    @7
    @42
    nnne0d
    divcan2d
    oveq2d
    @33
    c2
    @7
    @66
    @33
    c2
    @54
    recnd
    @83
    @43
    expmuld
    eqtr3d
    oveq2d
    eqtrd
    @33
    @78
    @79
    @76
    @74
    wceq
    @77
    ax-1cn
    @28
    c1
    negsubdi2
    sylancl
    oveq12d
    @33
    @2
    @29
    @36
    @48
    @62
    div2negd
    3eqtr2d
    @33
    @68
    @70
    vn
    @33
    cc0
    @67
    fzfid
    @33
    @37
    @69
    cn0
    wcel
    @70
    cz
    wcel
    @69
    @68
    wcel
    @45
    @69
    @67
    elfznn0
    @28
    @69
    zexpcl
    syl2an
    fsumzcl
    eqeltrrd
    @33
    c1
    @29
    cmul
    co
    #
    @2
    clt
    wbr
    #
    @65
    @33
    @87
    @29
    @2
    clt
    @33
    @29
    @48
    mulid2d
    @33
    @28
    @1
    c1
    @58
    @85
    @51
    @33
    @7
    cP
    clt
    wbr
    #
    @28
    @1
    clt
    wbr
    @27
    @89
    @8
    @27
    @55
    c2
    @7
    cle
    wbr
    #
    @89
    @4
    @26
    @55
    @90
    @89
    w3a
    #
    @4
    c2
    cz
    wcel
    @0
    @26
    @91
    wb
    2z
    @13
    @7
    c2
    cP
    elfzm11
    sylancr
    biimpa
    simp3d
    adantr
    @33
    c2
    @7
    cP
    @54
    @56
    @4
    @0
    @26
    @8
    @13
    ad2antrr
    @57
    ltexp2d
    mpbid
    ltsub1dd
    eqbrtrd
    @33
    c1
    cr
    wcel
    @2
    cr
    wcel
    @29
    cr
    wcel
    @49
    @88
    @65
    wb
    @51
    @33
    @2
    @35
    nnred
    @47
    @60
    c1
    @2
    @29
    ltmuldiv
    syl112anc
    mpbid
    @30
    eluz2b1
    sylanbrc
    @29
    @30
    nprm
    syl2anc
    pm2.65da
    ralrimiva
    vk
    cP
    isprm3
    sylanbrc
end
