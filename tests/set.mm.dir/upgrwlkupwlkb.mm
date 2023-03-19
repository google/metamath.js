include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cupwlks.mm"
include "upgrwlkupwlk.mm"
include "ex.mm"
include "upwlkwlk.mm"
include "impbid1.mm"

theorem upgrwlkupwlkb
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( G e. UPGraph -> ( F ( Walks ` G ) P <-> F ( UPWalks ` G ) P ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cP
    cG
    cupwlks
    cfv
    wbr
    #
    @0
    @1
    @2
    cP
    cF
    cG
    upgrwlkupwlk
    ex
    cP
    cF
    cG
    upwlkwlk
    impbid1
end
