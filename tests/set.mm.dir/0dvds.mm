include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "0z.mm"
include "divides.mm"
include "mpan.mm"
include "zcn.mm"
include "mul01d.mm"
include "eqtr2.mm"
include "sylan2.mm"
include "ancoms.mm"
include "rexlimiva.mm"
include "syl6bi.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "breq2.mm"
include "mpbiri.mm"
include "impbid1.mm"

theorem 0dvds
  let cN: class N
  let vn: setvar n


  assert |- ( N e. ZZ -> ( 0 || N <-> N = 0 ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    cN
    cdvds
    wbr
    #
    cN
    cc0
    wceq
    #
    @0
    @1
    vn
    cv
    #
    cc0
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @2
    cc0
    cz
    wcel
    #
    @0
    @1
    @6
    wb
    0z
    vn
    cc0
    cN
    divides
    mpan
    @5
    @2
    vn
    cz
    @5
    @3
    cz
    wcel
    #
    @2
    @8
    @5
    @4
    cc0
    wceq
    @2
    @8
    @3
    @3
    zcn
    mul01d
    @4
    cN
    cc0
    eqtr2
    sylan2
    ancoms
    rexlimiva
    syl6bi
    @2
    @1
    cc0
    cc0
    cdvds
    wbr
    #
    @7
    @9
    0z
    cc0
    dvds0
    ax-mp
    cN
    cc0
    cc0
    cdvds
    breq2
    mpbiri
    impbid1
end
