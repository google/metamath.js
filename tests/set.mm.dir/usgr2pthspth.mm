include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cpths.mm"
include "wbr.mm"
include "cspths.mm"
include "ctrls.mm"
include "pthistrl.mm"
include "usgr2trlspth.mm"
include "syl5ib.mm"
include "spthispth.mm"
include "impbid1.mm"

theorem usgr2pthspth
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( G e. USGraph /\ ( # ` F ) = 2 ) -> ( F ( Paths ` G ) P <-> F ( SPaths ` G ) P ) )

  proof
    cG
    cusgr
    wcel
    cF
    chash
    cfv
    c2
    wceq
    wa
    #
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    @1
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    @0
    @2
    cP
    cF
    cG
    pthistrl
    cP
    cF
    cG
    usgr2trlspth
    syl5ib
    cP
    cF
    cG
    spthispth
    impbid1
end
