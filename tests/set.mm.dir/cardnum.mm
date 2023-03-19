include "com.mm"
include "cale.mm"
include "crn.mm"
include "cun.mm"
include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "iscard3.mm"
include "bicomi.mm"
include "abbi2i.mm"
include "eqcomi.mm"

theorem cardnum
  let vx: setvar x


  assert |- { x | ( card ` x ) = x } = ( _om u. ran aleph )

  proof
    com
    cale
    crn
    cun
    #
    vx
    cv
    #
    ccrd
    cfv
    @1
    wceq
    #
    vx
    cab
    @2
    vx
    @0
    @2
    @1
    @0
    wcel
    @1
    iscard3
    bicomi
    abbi2i
    eqcomi
end
