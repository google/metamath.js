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
include "c1.mm"
include "cdc.mm"
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
include "10nn.mm"
include "nnzi.mm"
include "elfznn0.mm"
include "adantl.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "zmulcld.mm"
include "fsumzcl.mm"
include "zsubcld.mm"
include "cneg.mm"
include "c9.mm"
include "caddc.mm"
include "ax-1cn.mm"
include "nncni.mm"
include "negsubdi2i.mm"
include "9p1e10.mm"
include "eqcomi.mm"
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
include "1lt10.mm"
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
include "mp3an12i.mm"
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
include "mp3an2i.mm"
include "muls1d.mm"
include "breqtrd.mm"
include "fsumdvds.mm"
include "fsumsub.mm"
include "dvdssub2.mm"
include "syl31anc.mm"

theorem 3dvds
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vj: setvar j

  disjoint F k
  disjoint N k
  disjoint j k
  disjoint F j
  disjoint N j
  assert |- ( ( N e. NN0 /\ F : ( 0 ... N ) --> ZZ ) -> ( 3 || sum_ k e. ( 0 ... N ) ( ( F ` k ) x. ( ; 1 0 ^ k ) ) <-> 3 || sum_ k e. ( 0 ... N ) ( F ` k ) ) )

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
    c1
    cc0
    cdc
    #
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
    @10
    @11
    cmin
    co
    #
    cdvds
    wbr
    c3
    @10
    cdvds
    wbr
    c3
    @11
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
    @9
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
    @8
    @2
    @15
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
    @16
    @7
    cz
    wcel
    #
    @5
    cn0
    wcel
    #
    @8
    cz
    wcel
    #
    @7
    10nn
    nnzi
    #
    @15
    @20
    @3
    @5
    cN
    elfznn0
    adantl
    #
    @7
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
    @14
    @18
    fsumzcl
    @3
    c3
    @1
    @9
    @6
    cmin
    co
    #
    vk
    csu
    @12
    cdvds
    @3
    @1
    @27
    vk
    c3
    @14
    @13
    @16
    @9
    @6
    @26
    @18
    zsubcld
    @16
    c3
    @6
    @8
    c1
    cmin
    co
    #
    cmul
    co
    #
    @27
    cdvds
    @16
    c3
    @28
    cdvds
    wbr
    #
    c3
    @29
    cdvds
    wbr
    #
    @16
    @20
    @30
    @23
    @20
    c3
    c3
    cmul
    co
    #
    @28
    cdvds
    wbr
    #
    @30
    @20
    @32
    c1
    @7
    cmin
    co
    #
    cneg
    #
    @28
    cdvds
    @35
    c9
    @32
    @35
    @7
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
    @7
    ax-1cn
    @7
    10nn
    nncni
    #
    negsubdi2i
    @7
    @36
    c1
    cmin
    @36
    @7
    9p1e10
    eqcomi
    oveq1i
    c9
    c1
    9cn
    ax-1cn
    pncan3oi
    3eqtri
    3t3e9
    eqtr4i
    @20
    @34
    @28
    cdvds
    wbr
    #
    @35
    @28
    cdvds
    wbr
    #
    @20
    @38
    @34
    @28
    cneg
    #
    cdvds
    wbr
    #
    @20
    @34
    c1
    @8
    cmin
    co
    #
    @40
    cdvds
    @20
    @34
    @42
    cdvds
    wbr
    #
    @42
    @34
    cdiv
    co
    #
    cz
    wcel
    #
    @20
    cc0
    @5
    c1
    cmin
    co
    #
    cfz
    co
    #
    @7
    vj
    cv
    #
    cexp
    co
    #
    vj
    csu
    @44
    cz
    @20
    @7
    vj
    @5
    @7
    cc
    wcel
    @20
    @37
    a1i
    @7
    c1
    wne
    @20
    c1
    @7
    1re
    1lt10
    gtneii
    a1i
    @20
    id
    #
    geoser
    @20
    @47
    @49
    vj
    @20
    cc0
    @46
    fzfid
    @20
    @48
    @47
    wcel
    #
    wa
    @19
    @48
    cn0
    wcel
    #
    @49
    cz
    wcel
    @22
    @51
    @52
    @20
    @48
    @46
    elfznn0
    adantl
    @7
    @48
    zexpcl
    sylancr
    fsumzcl
    eqeltrrd
    @34
    cz
    wcel
    #
    @34
    cc0
    wne
    #
    @20
    @42
    cz
    wcel
    #
    @43
    @45
    wb
    c1
    cz
    wcel
    #
    @19
    @53
    1z
    @22
    c1
    @7
    zsubcl
    mp2an
    #
    @54
    c1
    @7
    wne
    c1
    @7
    1re
    1lt10
    ltneii
    @34
    cc0
    c1
    @7
    c1
    @7
    ax-1cn
    @37
    subeq0i
    necon3bii
    mpbir
    @20
    @56
    @21
    @55
    1z
    @20
    @19
    @20
    @21
    @22
    @50
    @24
    sylancr
    #
    c1
    @8
    zsubcl
    sylancr
    @34
    @42
    dvdsval2
    mp3an12i
    mpbird
    @20
    @8
    cc
    wcel
    c1
    cc
    wcel
    @40
    @42
    wceq
    @20
    @8
    @58
    zcnd
    ax-1cn
    @8
    c1
    negsubdi2
    sylancl
    breqtrrd
    @20
    @53
    @28
    cz
    wcel
    #
    @38
    @41
    wb
    @57
    @20
    @21
    @59
    @58
    @8
    peano2zm
    #
    syl
    #
    @34
    @28
    dvdsnegb
    sylancr
    mpbird
    @20
    @53
    @59
    @38
    @39
    wb
    @57
    @61
    @34
    @28
    negdvdsb
    sylancr
    mpbid
    syl5eqbrr
    @4
    @4
    @20
    @59
    @33
    @30
    wi
    3z
    3z
    @61
    c3
    c3
    @28
    muldvds1
    mp3an12i
    mpd
    syl
    @4
    @16
    @17
    @59
    @30
    @31
    wi
    3z
    @18
    @16
    @21
    @59
    @25
    @60
    syl
    c3
    @6
    @28
    dvdsmultr2
    mp3an2i
    mpd
    @16
    @6
    @8
    @16
    @6
    @18
    zcnd
    #
    @16
    @8
    @25
    zcnd
    muls1d
    breqtrd
    fsumdvds
    @3
    @1
    @9
    @6
    vk
    @14
    @16
    @9
    @26
    zcnd
    @62
    fsumsub
    breqtrd
    c3
    @10
    @11
    dvdssub2
    syl31anc
end
