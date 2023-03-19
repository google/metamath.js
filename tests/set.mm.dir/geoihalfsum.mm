include "cn.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "wcel.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "nnz.mm"
include "exprecd.mm"
include "sumeq2i.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "halfcn.mm"
include "cr.mm"
include "cle.mm"
include "halfre.mm"
include "0le1.mm"
include "wb.mm"
include "1re.mm"
include "2re.mm"
include "2pos.mm"
include "ge0div.mm"
include "mp3an.mm"
include "mpbi.mm"
include "absid.mm"
include "mp2an.mm"
include "halflt1.mm"
include "eqbrtri.mm"
include "geoisum1.mm"
include "1mhlfehlf.mm"
include "oveq2i.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "divne0i.mm"
include "dividi.mm"
include "3eqtri.mm"
include "eqtr3i.mm"

theorem geoihalfsum
  let vk: setvar k


  assert |- sum_ k e. NN ( 1 / ( 2 ^ k ) ) = 1

  proof
    cn
    c1
    c2
    cdiv
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cn
    c1
    c2
    @1
    cexp
    co
    cdiv
    co
    #
    vk
    csu
    c1
    cn
    @2
    @4
    vk
    @1
    cn
    wcel
    #
    c2
    @1
    c2
    cc
    wcel
    @5
    2cn
    a1i
    c2
    cc0
    wne
    @5
    2ne0
    a1i
    @1
    nnz
    exprecd
    sumeq2i
    @3
    @0
    c1
    @0
    cmin
    co
    #
    cdiv
    co
    #
    @0
    @0
    cdiv
    co
    c1
    @0
    cc
    wcel
    @0
    cabs
    cfv
    #
    c1
    clt
    wbr
    @3
    @7
    wceq
    halfcn
    @8
    @0
    c1
    clt
    @0
    cr
    wcel
    cc0
    @0
    cle
    wbr
    #
    @8
    @0
    wceq
    halfre
    cc0
    c1
    cle
    wbr
    #
    @9
    0le1
    c1
    cr
    wcel
    c2
    cr
    wcel
    cc0
    c2
    clt
    wbr
    @10
    @9
    wb
    1re
    2re
    2pos
    c1
    c2
    ge0div
    mp3an
    mpbi
    @0
    absid
    mp2an
    halflt1
    eqbrtri
    @0
    vk
    geoisum1
    mp2an
    @6
    @0
    @0
    cdiv
    1mhlfehlf
    oveq2i
    @0
    halfcn
    c1
    c2
    ax-1cn
    2cn
    ax-1ne0
    2ne0
    divne0i
    dividi
    3eqtri
    eqtr3i
end
