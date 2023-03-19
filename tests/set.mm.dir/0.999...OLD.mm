include "cn.mm"
include "c9.mm"
include "c10.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "c1.mm"
include "cmul.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "cn0.mm"
include "10reOLD.mm"
include "recni.mm"
include "nnnn0.mm"
include "expcl.mm"
include "sylancr.mm"
include "a1i.mm"
include "10posOLD.mm"
include "gt0ne0ii.mm"
include "nnz.mm"
include "expne0d.mm"
include "9cn.mm"
include "divrec.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "exprecd.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "sumeq2i.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "rereccli.mm"
include "cle.mm"
include "0re.mm"
include "recgt0ii.mm"
include "ltleii.mm"
include "absidi.mm"
include "ax-mp.mm"
include "1lt10OLD.mm"
include "cr.mm"
include "wb.mm"
include "recgt1.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqbrtri.mm"
include "geoisum1c.mm"
include "mp3an.mm"
include "divreci.mm"
include "divcan2i.mm"
include "ax-1cn.mm"
include "subdii.mm"
include "mulid1i.mm"
include "recidi.mm"
include "oveq12i.mm"
include "caddc.mm"
include "addcomi.mm"
include "df-10OLD.mm"
include "eqtr4i.mm"
include "subaddrii.mm"
include "3eqtrri.mm"
include "eqtri.mm"
include "9re.mm"
include "redivcli.mm"
include "subcli.mm"
include "mulcani.mm"
include "9pos.mm"
include "divgt0ii.mm"
include "dividi.mm"
include "3eqtr2i.mm"

theorem 0.999...OLD
  let vk: setvar k


  assert |- sum_ k e. NN ( 9 / ( 10 ^ k ) ) = 1

  proof
    cn
    c9
    c10
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    vk
    csu
    cn
    c9
    c1
    c10
    cdiv
    co
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c1
    cn
    @2
    @5
    vk
    @0
    cn
    wcel
    #
    @2
    c9
    c1
    @1
    cdiv
    co
    #
    cmul
    co
    #
    @5
    @7
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    #
    @2
    @9
    wceq
    #
    @7
    c10
    cc
    wcel
    #
    @0
    cn0
    wcel
    @10
    c10
    10reOLD
    recni
    #
    @0
    nnnn0
    c10
    @0
    expcl
    sylancr
    @7
    c10
    @0
    @13
    @7
    @14
    a1i
    #
    c10
    cc0
    wne
    @7
    c10
    10reOLD
    10posOLD
    gt0ne0ii
    #
    a1i
    #
    @0
    nnz
    #
    expne0d
    c9
    cc
    wcel
    #
    @10
    @11
    @12
    9cn
    c9
    @1
    divrec
    mp3an1
    syl2anc
    @7
    @4
    @8
    c9
    cmul
    @7
    c10
    @0
    @15
    @17
    @18
    exprecd
    oveq2d
    eqtr4d
    sumeq2i
    @6
    c9
    @3
    cmul
    co
    #
    c1
    @3
    cmin
    co
    #
    cdiv
    co
    #
    c9
    c10
    cdiv
    co
    #
    @23
    cdiv
    co
    c1
    @19
    @3
    cc
    wcel
    @3
    cabs
    cfv
    #
    c1
    clt
    wbr
    @6
    @22
    wceq
    9cn
    @3
    c10
    10reOLD
    @16
    rereccli
    #
    recni
    #
    @24
    @3
    c1
    clt
    cc0
    @3
    cle
    wbr
    @24
    @3
    wceq
    cc0
    @3
    0re
    @25
    c10
    10reOLD
    10posOLD
    recgt0ii
    ltleii
    @3
    @25
    absidi
    ax-mp
    c1
    c10
    clt
    wbr
    #
    @3
    c1
    clt
    wbr
    #
    1lt10OLD
    c10
    cr
    wcel
    cc0
    c10
    clt
    wbr
    @27
    @28
    wb
    10reOLD
    10posOLD
    c10
    recgt1
    mp2an
    mpbi
    eqbrtri
    c9
    @3
    vk
    geoisum1c
    mp3an
    @23
    @20
    @23
    @21
    cdiv
    c9
    c10
    9cn
    @14
    @16
    divreci
    c10
    @23
    cmul
    co
    #
    c10
    @21
    cmul
    co
    #
    wceq
    @23
    @21
    wceq
    @29
    c9
    @30
    c9
    c10
    9cn
    @14
    @16
    divcan2i
    @30
    c10
    c1
    cmul
    co
    #
    c10
    @3
    cmul
    co
    #
    cmin
    co
    c10
    c1
    cmin
    co
    c9
    c10
    c1
    @3
    @14
    ax-1cn
    @26
    subdii
    @31
    c10
    @32
    c1
    cmin
    c10
    @14
    mulid1i
    c10
    @14
    @16
    recidi
    oveq12i
    c10
    c1
    c9
    @14
    ax-1cn
    9cn
    c1
    c9
    caddc
    co
    c9
    c1
    caddc
    co
    c10
    c1
    c9
    ax-1cn
    9cn
    addcomi
    df-10OLD
    eqtr4i
    subaddrii
    3eqtrri
    eqtri
    @23
    @21
    c10
    @23
    c9
    c10
    9re
    10reOLD
    @16
    redivcli
    #
    recni
    #
    c1
    @3
    ax-1cn
    @26
    subcli
    @14
    @16
    mulcani
    mpbi
    oveq12i
    @23
    @34
    @23
    @33
    c9
    c10
    9re
    10reOLD
    9pos
    10posOLD
    divgt0ii
    gt0ne0ii
    dividi
    3eqtr2i
    eqtri
end
