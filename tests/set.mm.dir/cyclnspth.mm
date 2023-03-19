include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cspths.mm"
include "wn.mm"
include "cpths.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "iscycl.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "relpths.mm"
include "brrelexi.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "bicomd.mm"
include "syl.mm"
include "biimpa.mm"
include "spthdep.mm"
include "neneqd.mm"
include "expcom.mm"
include "con2d.mm"
include "impancom.mm"
include "sylbi.mm"
include "com12.mm"

theorem cyclnspth
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F =/= (/) -> ( F ( Cycles ` G ) P -> -. F ( SPaths ` G ) P ) )

  proof
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    #
    cF
    c0
    wne
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    wn
    #
    @0
    cF
    cP
    cG
    cpths
    cfv
    #
    wbr
    #
    cc0
    cP
    cfv
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    wceq
    #
    wa
    @1
    @3
    wi
    cP
    cF
    cG
    iscycl
    @5
    @1
    @9
    @3
    @5
    @1
    wa
    #
    @2
    @9
    @10
    @7
    cc0
    wne
    #
    @2
    @9
    wn
    #
    wi
    @5
    @1
    @11
    @5
    cF
    cvv
    wcel
    #
    @1
    @11
    wb
    cF
    cP
    @4
    cG
    relpths
    brrelexi
    @13
    @11
    @1
    @13
    @7
    cc0
    cF
    c0
    cF
    cvv
    hasheq0
    necon3bid
    bicomd
    syl
    biimpa
    @2
    @11
    @12
    @2
    @11
    wa
    @6
    @8
    cP
    cF
    cG
    spthdep
    neneqd
    expcom
    syl
    con2d
    impancom
    sylbi
    com12
end
