include "cpo.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cple.mm"
include "ccnv.mm"
include "cvv.mm"
include "codu.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wceq.mm"
include "eqid.mm"
include "odubas.mm"
include "oduleval.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "posref.mm"
include "vex.mm"
include "brcnv.mm"
include "sylibr.mm"
include "w3a.mm"
include "weq.mm"
include "anbi12ci.mm"
include "posasymb.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "wi.mm"
include "3anrev.mm"
include "postr.mm"
include "sylan2b.mm"
include "3imtr4g.mm"
include "isposd.mm"

theorem odupos
  let cD: class D
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cV: class V
  assume odupos.d: |- D = ( ODual ` O )


  assert |- ( O e. Poset -> D e. Poset )

  proof
    cO
    cpo
    wcel
    #
    va
    vb
    vc
    cO
    cbs
    cfv
    #
    cD
    cO
    cple
    cfv
    #
    ccnv
    #
    cD
    cvv
    wcel
    @0
    cD
    cO
    codu
    cfv
    cvv
    odupos.d
    cO
    codu
    fvex
    eqeltri
    a1i
    @1
    cD
    cbs
    cfv
    wceq
    @0
    @1
    cD
    cO
    odupos.d
    @1
    eqid
    #
    odubas
    a1i
    @3
    cD
    cple
    cfv
    wceq
    @0
    cD
    @2
    cO
    odupos.d
    @2
    eqid
    #
    oduleval
    a1i
    @0
    va
    cv
    #
    @1
    wcel
    #
    wa
    @6
    @6
    @2
    wbr
    @6
    @6
    @3
    wbr
    @1
    cO
    @2
    @6
    @4
    @5
    posref
    @6
    @6
    @2
    va
    vex
    #
    @8
    brcnv
    sylibr
    @6
    vb
    cv
    #
    @3
    wbr
    #
    @9
    @6
    @3
    wbr
    #
    wa
    @6
    @9
    @2
    wbr
    #
    @9
    @6
    @2
    wbr
    #
    wa
    #
    @0
    @7
    @9
    @1
    wcel
    #
    w3a
    #
    va
    vb
    weq
    #
    @10
    @13
    @11
    @12
    @6
    @9
    @2
    @8
    vb
    vex
    #
    brcnv
    #
    @9
    @6
    @2
    @18
    @8
    brcnv
    anbi12ci
    @16
    @14
    @17
    @1
    cO
    @2
    @6
    @9
    @4
    @5
    posasymb
    biimpd
    syl5bi
    @0
    @7
    @15
    vc
    cv
    #
    @1
    wcel
    #
    w3a
    #
    wa
    @20
    @9
    @2
    wbr
    #
    @13
    wa
    #
    @20
    @6
    @2
    wbr
    #
    @10
    @9
    @20
    @3
    wbr
    #
    wa
    @6
    @20
    @3
    wbr
    @22
    @0
    @21
    @15
    @7
    w3a
    @24
    @25
    wi
    @7
    @15
    @21
    3anrev
    @1
    cO
    @2
    @20
    @9
    @6
    @4
    @5
    postr
    sylan2b
    @10
    @13
    @26
    @23
    @19
    @9
    @20
    @2
    @18
    vc
    vex
    #
    brcnv
    anbi12ci
    @6
    @20
    @2
    @8
    @27
    brcnv
    3imtr4g
    isposd
end
