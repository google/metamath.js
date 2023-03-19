include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "cbits.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cv.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "clt.mm"
include "simpl.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "simpr.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "biantrurd.mm"
include "wb.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "bitsval2.mm"
include "syl2anc.mm"
include "biantrud.mm"
include "cmin.mm"
include "2z.mm"
include "zred.mm"
include "nndivred.mm"
include "flcld.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "2cnd.mm"
include "expp1d.mm"
include "cuz.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "cle.mm"
include "adantr.mm"
include "nn0ltp1le.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "dvdsexp.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"
include "cr.mm"
include "crp.mm"
include "nnrpd.mm"
include "moddifz.mm"
include "wne.mm"
include "nnzd.mm"
include "2ne0.mm"
include "expne0d.mm"
include "zsubcld.mm"
include "dvdsval2.mm"
include "mpbird.mm"
include "wi.mm"
include "zmulcld.mm"
include "dvdstr.mm"
include "mp2and.mm"
include "zcnd.mm"
include "nncnd.mm"
include "divcan2d.mm"
include "breqtrrd.mm"
include "nn0red.mm"
include "ltled.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "pncan3d.mm"
include "oveq1d.mm"
include "divdird.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "fladdz.mm"
include "eqtrd.mm"
include "pncan2d.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "notbid.mm"
include "3bitr3d.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "2rp.mm"
include "rpexpcld.mm"
include "modcld.mm"
include "nn0ge0d.mm"
include "divge0d.mm"
include "rpred.mm"
include "modlt.mm"
include "1le2.mm"
include "lenltd.mm"
include "leexp2ad.mm"
include "ltletrd.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "1red.mm"
include "ltdivmuld.mm"
include "1e0p1.mm"
include "syl6breq.mm"
include "rerpdivcld.mm"
include "0z.mm"
include "flbi.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "syl5breqr.mm"
include "intnand.mm"
include "2thd.mm"
include "con2bid.mm"
include "pm2.61dan.mm"
include "bitr3d.mm"
include "an12.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "3anass.mm"
include "elfzo2.mm"
include "elnn0uz.mm"
include "3anbi1i.mm"
include "3bitr2i.mm"
include "anbi2i.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "bitsval.mm"
include "elin.mm"
include "eqrdv.mm"

theorem bitsmod
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let vn: setvar n


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( bits ` ( N mod ( 2 ^ M ) ) ) = ( ( bits ` N ) i^i ( 0 ..^ M ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    vx
    cN
    c2
    cM
    cexp
    co
    #
    cmo
    co
    #
    cbits
    cfv
    #
    cN
    cbits
    cfv
    #
    cc0
    cM
    cfzo
    co
    #
    cin
    #
    @2
    @4
    cz
    wcel
    #
    vx
    cv
    #
    cn0
    wcel
    #
    c2
    @4
    c2
    @10
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    w3a
    #
    @10
    @6
    wcel
    #
    @10
    @7
    wcel
    #
    wa
    #
    @10
    @5
    wcel
    @10
    @8
    wcel
    @2
    @9
    @11
    @16
    wa
    #
    wa
    #
    @11
    @18
    cM
    cz
    wcel
    #
    @10
    cM
    clt
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    @17
    @20
    @2
    @21
    @22
    @27
    @2
    @9
    @21
    @2
    @4
    @2
    cN
    @3
    @0
    @1
    simpl
    #
    @2
    c2
    cM
    c2
    cn
    wcel
    #
    @2
    2nn
    a1i
    @0
    @1
    simpr
    nnexpcld
    #
    zmodcld
    #
    nn0zd
    #
    biantrurd
    @2
    @11
    @16
    @26
    @2
    @11
    wa
    #
    @16
    @23
    @18
    @24
    wa
    #
    wa
    #
    @26
    @33
    @34
    @16
    @35
    @33
    @24
    @34
    @16
    wb
    @33
    @24
    wa
    #
    @18
    c2
    cN
    @12
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    @34
    @16
    @36
    @0
    @11
    @18
    @40
    wb
    @2
    @0
    @11
    @24
    @28
    ad2antrr
    #
    @2
    @11
    @24
    simplr
    #
    @10
    cN
    bitsval2
    syl2anc
    @36
    @24
    @18
    @33
    @24
    simpr
    #
    biantrud
    @36
    @39
    @15
    @36
    c2
    cz
    wcel
    #
    @38
    cz
    wcel
    @14
    cz
    wcel
    c2
    @38
    @14
    cmin
    co
    #
    cdvds
    wbr
    @39
    @15
    wb
    @44
    @36
    2z
    a1i
    #
    @36
    @37
    @36
    cN
    @12
    @36
    cN
    @41
    zred
    #
    @36
    c2
    @10
    @29
    @36
    2nn
    a1i
    @42
    nnexpcld
    #
    nndivred
    flcld
    @36
    @13
    @36
    @4
    @12
    @36
    @4
    @2
    @9
    @11
    @24
    @32
    ad2antrr
    #
    zred
    @48
    nndivred
    #
    flcld
    #
    @36
    c2
    cN
    @4
    cmin
    co
    #
    @12
    cdiv
    co
    #
    @45
    cdvds
    @36
    @12
    c2
    cmul
    co
    #
    @12
    @53
    cmul
    co
    #
    cdvds
    wbr
    #
    c2
    @53
    cdvds
    wbr
    #
    @36
    @54
    @52
    @55
    cdvds
    @36
    @54
    @3
    cdvds
    wbr
    #
    @3
    @52
    cdvds
    wbr
    #
    @54
    @52
    cdvds
    wbr
    #
    @36
    c2
    @10
    c1
    caddc
    co
    #
    cexp
    co
    #
    @54
    @3
    cdvds
    @36
    c2
    @10
    @36
    2cnd
    #
    @42
    expp1d
    @36
    @44
    @61
    cn0
    wcel
    cM
    @61
    cuz
    cfv
    wcel
    #
    @62
    @3
    cdvds
    wbr
    @46
    @36
    @10
    c1
    @42
    c1
    cn0
    wcel
    @36
    1nn0
    a1i
    nn0addcld
    #
    @36
    @61
    cz
    wcel
    @23
    @61
    cM
    cle
    wbr
    #
    @64
    @36
    @61
    @65
    nn0zd
    @36
    cM
    @33
    @1
    @24
    @0
    @1
    @11
    simplr
    #
    adantr
    #
    nn0zd
    #
    @36
    @24
    @66
    @43
    @36
    @11
    @1
    @24
    @66
    wb
    @42
    @68
    @10
    cM
    nn0ltp1le
    syl2anc
    mpbid
    @61
    cM
    eluz2
    syl3anbrc
    c2
    @61
    cM
    dvdsexp
    syl3anc
    eqbrtrrd
    @36
    @59
    @52
    @3
    cdiv
    co
    cz
    wcel
    #
    @36
    cN
    cr
    wcel
    #
    @3
    crp
    wcel
    #
    @70
    @47
    @36
    @3
    @2
    @3
    cn
    wcel
    @11
    @24
    @30
    ad2antrr
    #
    nnrpd
    cN
    @3
    moddifz
    syl2anc
    @36
    @3
    cz
    wcel
    #
    @3
    cc0
    wne
    @52
    cz
    wcel
    #
    @59
    @70
    wb
    @36
    @3
    @73
    nnzd
    #
    @36
    c2
    cM
    @63
    c2
    cc0
    wne
    @36
    2ne0
    a1i
    #
    @69
    expne0d
    @36
    cN
    @4
    @41
    @49
    zsubcld
    #
    @3
    @52
    dvdsval2
    syl3anc
    mpbird
    #
    @36
    @54
    cz
    wcel
    @74
    @75
    @58
    @59
    wa
    @60
    wi
    @36
    @12
    c2
    @36
    @12
    @48
    nnzd
    #
    @46
    zmulcld
    @76
    @78
    @54
    @3
    @52
    dvdstr
    syl3anc
    mp2and
    @36
    @52
    @12
    @36
    @52
    @78
    zcnd
    #
    @36
    @12
    @48
    nncnd
    #
    @36
    c2
    @10
    @63
    @77
    @36
    @10
    @42
    nn0zd
    #
    expne0d
    #
    divcan2d
    breqtrrd
    @36
    @44
    @53
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @12
    cc0
    wne
    #
    @56
    @57
    wb
    @46
    @36
    @12
    @52
    cdvds
    wbr
    #
    @85
    @36
    @12
    @3
    cdvds
    wbr
    #
    @59
    @88
    @36
    @44
    @11
    cM
    @10
    cuz
    cfv
    wcel
    #
    @89
    @46
    @42
    @36
    @10
    cz
    wcel
    #
    @23
    @10
    cM
    cle
    wbr
    @90
    @83
    @69
    @36
    @10
    cM
    @36
    @10
    @42
    nn0red
    @36
    cM
    @68
    nn0red
    @43
    ltled
    @10
    cM
    eluz2
    syl3anbrc
    c2
    @10
    cM
    dvdsexp
    syl3anc
    @79
    @36
    @86
    @74
    @75
    @89
    @59
    wa
    @88
    wi
    @80
    @76
    @78
    @12
    @3
    @52
    dvdstr
    syl3anc
    mp2and
    @36
    @86
    @87
    @75
    @88
    @85
    wb
    @80
    @84
    @78
    @12
    @52
    dvdsval2
    syl3anc
    mpbid
    #
    @80
    @84
    @12
    c2
    @53
    dvdscmulr
    syl112anc
    mpbid
    @36
    @45
    @14
    @53
    caddc
    co
    #
    @14
    cmin
    co
    @53
    @36
    @38
    @93
    @14
    cmin
    @36
    @38
    @13
    @53
    caddc
    co
    #
    cfl
    cfv
    #
    @93
    @36
    @37
    @94
    cfl
    @36
    @4
    @52
    caddc
    co
    #
    @12
    cdiv
    co
    @37
    @94
    @36
    @96
    cN
    @12
    cdiv
    @36
    @4
    cN
    @36
    @4
    @49
    zcnd
    #
    @36
    cN
    @41
    zcnd
    pncan3d
    oveq1d
    @36
    @4
    @52
    @12
    @97
    @81
    @82
    @84
    divdird
    eqtr3d
    fveq2d
    @36
    @13
    cr
    wcel
    #
    @85
    @95
    @93
    wceq
    @50
    @92
    @13
    @53
    fladdz
    syl2anc
    eqtrd
    oveq1d
    @36
    @14
    @53
    @36
    @14
    @51
    zcnd
    @36
    @53
    @92
    zcnd
    pncan2d
    eqtrd
    breqtrrd
    c2
    @38
    @14
    dvdssub2
    syl31anc
    notbid
    3bitr3d
    @33
    @24
    wn
    #
    wa
    #
    @15
    @34
    @100
    @15
    @34
    wn
    @100
    c2
    cc0
    @14
    cdvds
    @44
    c2
    cc0
    cdvds
    wbr
    2z
    c2
    dvds0
    ax-mp
    @100
    @14
    cc0
    wceq
    #
    cc0
    @13
    cle
    wbr
    #
    @13
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @100
    @4
    @12
    @100
    cN
    @3
    @100
    cN
    @2
    @0
    @11
    @99
    @28
    ad2antrr
    zred
    #
    @100
    c2
    cM
    c2
    crp
    wcel
    @100
    2rp
    a1i
    #
    @33
    @23
    @99
    @33
    cM
    @67
    nn0zd
    #
    adantr
    #
    rpexpcld
    #
    modcld
    #
    @100
    c2
    @10
    @106
    @100
    @10
    @2
    @11
    @99
    simplr
    #
    nn0zd
    #
    rpexpcld
    #
    @100
    @4
    @2
    @4
    cn0
    wcel
    @11
    @99
    @31
    ad2antrr
    nn0ge0d
    divge0d
    @100
    @13
    c1
    @103
    clt
    @100
    @13
    c1
    clt
    wbr
    @4
    @12
    c1
    cmul
    co
    #
    clt
    wbr
    @100
    @4
    @12
    @114
    clt
    @100
    @4
    @3
    @12
    @110
    @100
    @3
    @109
    rpred
    @100
    @12
    @113
    rpred
    @100
    @71
    @72
    @4
    @3
    clt
    wbr
    @105
    @109
    cN
    @3
    modlt
    syl2anc
    @100
    c2
    cM
    @10
    @100
    c2
    @106
    rpred
    c1
    c2
    cle
    wbr
    @100
    1le2
    a1i
    @100
    @23
    @91
    cM
    @10
    cle
    wbr
    #
    @10
    cM
    cuz
    cfv
    wcel
    @108
    @112
    @100
    @115
    @99
    @33
    @99
    simpr
    #
    @100
    cM
    @10
    @100
    cM
    @108
    zred
    @100
    @10
    @111
    nn0red
    lenltd
    mpbird
    cM
    @10
    eluz2
    syl3anbrc
    leexp2ad
    ltletrd
    @100
    @12
    @100
    @12
    @113
    rpcnd
    mulid1d
    breqtrrd
    @100
    @4
    c1
    @12
    @110
    @100
    1red
    @113
    ltdivmuld
    mpbird
    1e0p1
    syl6breq
    @100
    @98
    cc0
    cz
    wcel
    @101
    @102
    @104
    wa
    wb
    @100
    @4
    @12
    @110
    @113
    rerpdivcld
    0z
    @13
    cc0
    flbi
    sylancl
    mpbir2and
    syl5breqr
    @100
    @24
    @18
    @116
    intnand
    2thd
    con2bid
    pm2.61dan
    @33
    @23
    @34
    @107
    biantrurd
    bitr3d
    @23
    @18
    @24
    an12
    syl6bb
    pm5.32da
    bitr3d
    @9
    @11
    @16
    3anass
    @20
    @18
    @11
    @25
    wa
    #
    wa
    @27
    @19
    @117
    @18
    @19
    @10
    cc0
    cuz
    cfv
    wcel
    #
    @23
    @24
    w3a
    @11
    @23
    @24
    w3a
    @117
    @10
    cc0
    cM
    elfzo2
    @11
    @118
    @23
    @24
    @10
    elnn0uz
    3anbi1i
    @11
    @23
    @24
    3anass
    3bitr2i
    anbi2i
    @18
    @11
    @25
    an12
    bitri
    3bitr4g
    @10
    @4
    bitsval
    @10
    @6
    @7
    elin
    3bitr4g
    eqrdv
end
