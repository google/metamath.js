include "wcel.mm"
include "cpo.mm"
include "odupos.mm"
include "codu.mm"
include "cfv.mm"
include "eqid.mm"
include "cbs.mm"
include "cvv.mm"
include "fvexd.mm"
include "id.mm"
include "wceq.mm"
include "odubas.mm"
include "a1i.mm"
include "eqidd.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "ccnv.mm"
include "oduleval.mm"
include "eqcomi.mm"
include "breqi.mm"
include "vex.mm"
include "brcnv.mm"
include "3bitri.mm"
include "pospropd.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem oduposb
  let cD: class D
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume odupos.d: |- D = ( ODual ` O )


  assert |- ( O e. V -> ( O e. Poset <-> D e. Poset ) )

  proof
    cO
    cV
    wcel
    #
    cO
    cpo
    wcel
    #
    cD
    cpo
    wcel
    #
    cD
    cO
    odupos.d
    odupos
    @2
    cD
    codu
    cfv
    #
    cpo
    wcel
    @0
    @1
    @3
    cD
    @3
    eqid
    #
    odupos
    @0
    va
    vb
    cO
    cbs
    cfv
    #
    @3
    cO
    cvv
    cV
    @0
    cD
    codu
    fvexd
    @0
    id
    @5
    @3
    cbs
    cfv
    wceq
    @0
    @5
    @3
    cD
    @4
    @5
    cD
    cO
    odupos.d
    @5
    eqid
    odubas
    odubas
    a1i
    @0
    @5
    eqidd
    va
    cv
    #
    vb
    cv
    #
    @3
    cple
    cfv
    #
    wbr
    #
    @6
    @7
    cO
    cple
    cfv
    #
    wbr
    #
    wb
    @0
    @6
    @5
    wcel
    @7
    @5
    wcel
    wa
    wa
    @9
    @6
    @7
    @10
    ccnv
    #
    ccnv
    #
    wbr
    @7
    @6
    @12
    wbr
    @11
    @6
    @7
    @8
    @13
    @13
    @8
    @3
    @12
    cD
    @4
    cD
    @10
    cO
    odupos.d
    @10
    eqid
    oduleval
    oduleval
    eqcomi
    breqi
    @6
    @7
    @12
    va
    vex
    #
    vb
    vex
    #
    brcnv
    @7
    @6
    @10
    @15
    @14
    brcnv
    3bitri
    a1i
    pospropd
    syl5ib
    impbid2
end
