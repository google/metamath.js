include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cz.mm"
include "wf.mm"
include "wa.mm"
include "c3.mm"
include "cv.mm"
include "cfv.mm"
include "c10.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "3z.mm"
include "a1i.mm"
include "fzfid.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "10nnOLD.mm"
include "nnzi.mm"
include "elfznn0.mm"
include "adantl.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "zmulcld.mm"
include "fsumzcl.mm"
include "zsubcld.mm"
include "c1.mm"
include "cneg.mm"
include "c9.mm"
include "caddc.mm"
include "ax-1cn.mm"
include "nncni.mm"
include "negsubdi2i.mm"
include "df-10OLD.mm"
include "oveq1i.mm"
include "9cn.mm"
include "pncan3oi.mm"
include "3eqtri.mm"
include "3t3e9.mm"
include "eqtr4i.mm"
include "cdiv.mm"
include "cc.mm"
include "wne.mm"
include "1re.mm"
include "1lt10OLD.mm"
include "gtneii.mm"
include "id.mm"
include "geoser.mm"
include "eqeltrrd.mm"
include "1z.mm"
include "zsubcl.mm"
include "mp2an.mm"
include "ltneii.mm"
include "subeq0i.mm"
include "necon3bii.mm"
include "mpbir.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wceq.mm"
include "zcnd.mm"
include "negsubdi2.mm"
include "sylancl.mm"
include "breqtrrd.mm"
include "peano2zm.mm"
include "syl.mm"
include "dvdsnegb.mm"
include "negdvdsb.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "wi.mm"
include "muldvds1.mm"
include "mpd.mm"
include "dvdsmultr2.mm"
include "subdid.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "fsumdvds.mm"
include "fsumsub.mm"
include "dvdssub2.mm"
include "syl31anc.mm"

theorem 3dvdsOLD
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vj: setvar j

  disjoint F k
  disjoint N k
  disjoint j k
  disjoint F j
  disjoint N j
  assert |- ( ( N e. NN0 /\ F : ( 0 ... N ) --> ZZ ) -> ( 3 || sum_ k e. ( 0 ... N ) ( ( F ` k ) x. ( 10 ^ k ) ) <-> 3 || sum_ k e. ( 0 ... N ) ( F ` k ) ) )

  proof
    cN
    cn0
    wcel
    #
    cc0
    cN
    cfz
    co
    #
    cz
    cF
    wf
    #
    wa
    #
    c3
    cz
    wcel
    #
    @1
    vk
    cv
    #
    cF
    cfv
    #
    c10
    @5
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cz
    wcel
    @1
    @6
    vk
    csu
    #
    cz
    wcel
    c3
    @9
    @10
    cmin
    co
    #
    cdvds
    wbr
    c3
    @9
    cdvds
    wbr
    c3
    @10
    cdvds
    wbr
    wb
    @4
    @3
    3z
    a1i
    #
    @3
    @1
    @8
    vk
    @3
    cc0
    cN
    fzfid
    #
    @3
    @5
    @1
    wcel
    #
    wa
    #
    @6
    @7
    @2
    @14
    @6
    cz
    wcel
    #
    @0
    @1
    cz
    @5
    cF
    ffvelrn
    adantll
    #
    @15
    c10
    cz
    wcel
    #
    @5
    cn0
    wcel
    #
    @7
    cz
    wcel
    #
    c10
    10nnOLD
    nnzi
    #
    @14
    @19
    @3
    @5
    cN
    elfznn0
    adantl
    #
    c10
    @5
    zexpcl
    #
    sylancr
    #
    zmulcld
    #
    fsumzcl
    @3
    @1
    @6
    vk
    @13
    @17
    fsumzcl
    @3
    c3
    @1
    @8
    @6
    cmin
    co
    #
    vk
    csu
    @11
    cdvds
    @3
    @1
    @26
    vk
    c3
    @13
    @12
    @15
    @8
    @6
    @25
    @17
    zsubcld
    @15
    c3
    @6
    @7
    c1
    cmin
    co
    #
    cmul
    co
    #
    @26
    cdvds
    @15
    c3
    @27
    cdvds
    wbr
    #
    c3
    @28
    cdvds
    wbr
    #
    @15
    @19
    @29
    @22
    @19
    c3
    c3
    cmul
    co
    #
    @27
    cdvds
    wbr
    #
    @29
    @19
    @31
    c1
    c10
    cmin
    co
    #
    cneg
    #
    @27
    cdvds
    @34
    c9
    @31
    @34
    c10
    c1
    cmin
    co
    c9
    c1
    caddc
    co
    #
    c1
    cmin
    co
    c9
    c1
    c10
    ax-1cn
    c10
    10nnOLD
    nncni
    #
    negsubdi2i
    c10
    @35
    c1
    cmin
    df-10OLD
    oveq1i
    c9
    c1
    9cn
    ax-1cn
    pncan3oi
    3eqtri
    3t3e9
    eqtr4i
    @19
    @33
    @27
    cdvds
    wbr
    #
    @34
    @27
    cdvds
    wbr
    #
    @19
    @37
    @33
    @27
    cneg
    #
    cdvds
    wbr
    #
    @19
    @33
    c1
    @7
    cmin
    co
    #
    @39
    cdvds
    @19
    @33
    @41
    cdvds
    wbr
    #
    @41
    @33
    cdiv
    co
    #
    cz
    wcel
    #
    @19
    cc0
    @5
    c1
    cmin
    co
    #
    cfz
    co
    #
    c10
    vj
    cv
    #
    cexp
    co
    #
    vj
    csu
    @43
    cz
    @19
    c10
    vj
    @5
    c10
    cc
    wcel
    @19
    @36
    a1i
    c10
    c1
    wne
    @19
    c1
    c10
    1re
    1lt10OLD
    gtneii
    a1i
    @19
    id
    #
    geoser
    @19
    @46
    @48
    vj
    @19
    cc0
    @45
    fzfid
    @19
    @47
    @46
    wcel
    #
    wa
    @18
    @47
    cn0
    wcel
    #
    @48
    cz
    wcel
    @21
    @50
    @51
    @19
    @47
    @45
    elfznn0
    adantl
    c10
    @47
    zexpcl
    sylancr
    fsumzcl
    eqeltrrd
    @19
    @33
    cz
    wcel
    #
    @33
    cc0
    wne
    #
    @41
    cz
    wcel
    #
    @42
    @44
    wb
    @52
    @19
    c1
    cz
    wcel
    #
    @18
    @52
    1z
    @21
    c1
    c10
    zsubcl
    mp2an
    #
    a1i
    @53
    @19
    @53
    c1
    c10
    wne
    c1
    c10
    1re
    1lt10OLD
    ltneii
    @33
    cc0
    c1
    c10
    c1
    c10
    ax-1cn
    @36
    subeq0i
    necon3bii
    mpbir
    a1i
    @19
    @55
    @20
    @54
    1z
    @19
    @18
    @19
    @20
    @21
    @49
    @23
    sylancr
    #
    c1
    @7
    zsubcl
    sylancr
    @33
    @41
    dvdsval2
    syl3anc
    mpbird
    @19
    @7
    cc
    wcel
    c1
    cc
    wcel
    #
    @39
    @41
    wceq
    @19
    @7
    @57
    zcnd
    ax-1cn
    @7
    c1
    negsubdi2
    sylancl
    breqtrrd
    @19
    @52
    @27
    cz
    wcel
    #
    @37
    @40
    wb
    @56
    @19
    @20
    @59
    @57
    @7
    peano2zm
    #
    syl
    #
    @33
    @27
    dvdsnegb
    sylancr
    mpbird
    @19
    @52
    @59
    @37
    @38
    wb
    @56
    @61
    @33
    @27
    negdvdsb
    sylancr
    mpbid
    syl5eqbrr
    @19
    @4
    @4
    @59
    @32
    @29
    wi
    @4
    @19
    3z
    a1i
    #
    @62
    @61
    c3
    c3
    @27
    muldvds1
    syl3anc
    mpd
    syl
    @15
    @4
    @16
    @59
    @29
    @30
    wi
    @4
    @15
    3z
    a1i
    @17
    @15
    @20
    @59
    @24
    @60
    syl
    c3
    @6
    @27
    dvdsmultr2
    syl3anc
    mpd
    @15
    @28
    @8
    @6
    c1
    cmul
    co
    #
    cmin
    co
    @26
    @15
    @6
    @7
    c1
    @15
    @6
    @17
    zcnd
    #
    @15
    @7
    @24
    zcnd
    @58
    @15
    ax-1cn
    a1i
    subdid
    @15
    @63
    @6
    @8
    cmin
    @15
    @6
    @64
    mulid1d
    oveq2d
    eqtrd
    breqtrd
    fsumdvds
    @3
    @1
    @8
    @6
    vk
    @13
    @15
    @8
    @25
    zcnd
    @64
    fsumsub
    breqtrd
    c3
    @9
    @10
    dvdssub2
    syl31anc
end
