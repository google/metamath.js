include "cn.mm"
include "c9.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "wcel.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "9cn.mm"
include "cn0.mm"
include "10re.mm"
include "recni.mm"
include "nnnn0.mm"
include "expcl.mm"
include "sylancr.mm"
include "a1i.mm"
include "10pos.mm"
include "gt0ne0ii.mm"
include "nnz.mm"
include "expne0d.mm"
include "divrec.mm"
include "mp3an2i.mm"
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
include "1lt10.mm"
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
include "10m1e9.mm"
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

theorem 0.999...
  let vk: setvar k


  assert |- sum_ k e. NN ( 9 / ( ; 1 0 ^ k ) ) = 1

  proof
    cn
    c9
    c1
    cc0
    cdc
    #
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
    @0
    cdiv
    co
    #
    @1
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
    @3
    @6
    vk
    @1
    cn
    wcel
    #
    @3
    c9
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    @6
    c9
    cc
    wcel
    #
    @8
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    @3
    @10
    wceq
    9cn
    @8
    @0
    cc
    wcel
    #
    @1
    cn0
    wcel
    @12
    @0
    10re
    recni
    #
    @1
    nnnn0
    @0
    @1
    expcl
    sylancr
    @8
    @0
    @1
    @13
    @8
    @14
    a1i
    #
    @0
    cc0
    wne
    @8
    @0
    10re
    10pos
    gt0ne0ii
    #
    a1i
    #
    @1
    nnz
    #
    expne0d
    c9
    @2
    divrec
    mp3an2i
    @8
    @5
    @9
    c9
    cmul
    @8
    @0
    @1
    @15
    @17
    @18
    exprecd
    oveq2d
    eqtr4d
    sumeq2i
    @7
    c9
    @4
    cmul
    co
    #
    c1
    @4
    cmin
    co
    #
    cdiv
    co
    #
    c9
    @0
    cdiv
    co
    #
    @22
    cdiv
    co
    c1
    @11
    @4
    cc
    wcel
    @4
    cabs
    cfv
    #
    c1
    clt
    wbr
    @7
    @21
    wceq
    9cn
    @4
    @0
    10re
    @16
    rereccli
    #
    recni
    #
    @23
    @4
    c1
    clt
    cc0
    @4
    cle
    wbr
    @23
    @4
    wceq
    cc0
    @4
    0re
    @24
    @0
    10re
    10pos
    recgt0ii
    ltleii
    @4
    @24
    absidi
    ax-mp
    c1
    @0
    clt
    wbr
    #
    @4
    c1
    clt
    wbr
    #
    1lt10
    @0
    cr
    wcel
    cc0
    @0
    clt
    wbr
    @26
    @27
    wb
    10re
    10pos
    @0
    recgt1
    mp2an
    mpbi
    eqbrtri
    c9
    @4
    vk
    geoisum1c
    mp3an
    @22
    @19
    @22
    @20
    cdiv
    c9
    @0
    9cn
    @14
    @16
    divreci
    @0
    @22
    cmul
    co
    #
    @0
    @20
    cmul
    co
    #
    wceq
    @22
    @20
    wceq
    @28
    c9
    @29
    c9
    @0
    9cn
    @14
    @16
    divcan2i
    @29
    @0
    c1
    cmul
    co
    #
    @0
    @4
    cmul
    co
    #
    cmin
    co
    @0
    c1
    cmin
    co
    c9
    @0
    c1
    @4
    @14
    ax-1cn
    @25
    subdii
    @30
    @0
    @31
    c1
    cmin
    @0
    @14
    mulid1i
    @0
    @14
    @16
    recidi
    oveq12i
    10m1e9
    3eqtrri
    eqtri
    @22
    @20
    @0
    @22
    c9
    @0
    9re
    10re
    @16
    redivcli
    #
    recni
    #
    c1
    @4
    ax-1cn
    @25
    subcli
    @14
    @16
    mulcani
    mpbi
    oveq12i
    @22
    @33
    @22
    @32
    c9
    @0
    9re
    10re
    9pos
    10pos
    divgt0ii
    gt0ne0ii
    dividi
    3eqtr2i
    eqtri
end
