include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cc0.mm"
include "recgt1i.mm"
include "simprd.mm"
include "cle.mm"
include "wn.mm"
include "simpld.mm"
include "zgt0ge1.mm"
include "syl5ibcom.mm"
include "wb.mm"
include "1re.mm"
include "wne.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imdistani.mm"
include "gt0ne0.mm"
include "syl.mm"
include "rereccl.mm"
include "syldan.mm"
include "lenlt.mm"
include "sylancr.mm"
include "sylibd.mm"
include "mt2d.mm"

theorem recnz
  let cA: class A


  assert |- ( ( A e. RR /\ 1 < A ) -> -. ( 1 / A ) e. ZZ )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    c1
    cA
    cdiv
    co
    #
    cz
    wcel
    #
    @3
    c1
    clt
    wbr
    #
    @2
    cc0
    @3
    clt
    wbr
    #
    @5
    cA
    recgt1i
    #
    simprd
    @2
    @4
    c1
    @3
    cle
    wbr
    #
    @5
    wn
    #
    @2
    @6
    @4
    @8
    @2
    @6
    @5
    @7
    simpld
    @3
    zgt0ge1
    syl5ibcom
    @2
    c1
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @8
    @9
    wb
    1re
    @0
    @1
    cA
    cc0
    wne
    #
    @11
    @2
    @0
    cc0
    cA
    clt
    wbr
    #
    wa
    @12
    @0
    @1
    @13
    @0
    cc0
    c1
    clt
    wbr
    #
    @1
    @13
    0lt1
    cc0
    cr
    wcel
    @10
    @0
    @14
    @1
    wa
    @13
    wi
    0re
    1re
    cc0
    c1
    cA
    lttr
    mp3an12
    mpani
    imdistani
    cA
    gt0ne0
    syl
    cA
    rereccl
    syldan
    c1
    @3
    lenlt
    sylancr
    sylibd
    mt2d
end
