include "wcel.mm"
include "cc0.mm"
include "creps.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "cn0.mm"
include "0nn0.mm"
include "repswlen.mm"
include "mpan2.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "hasheq0.mm"
include "mp1i.mm"
include "mpbid.mm"

theorem repsw0
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( S repeatS 0 ) = (/) )

  proof
    cS
    cV
    wcel
    #
    cS
    cc0
    creps
    co
    #
    chash
    cfv
    cc0
    wceq
    #
    @1
    c0
    wceq
    #
    @0
    cc0
    cn0
    wcel
    @2
    0nn0
    cS
    cc0
    cV
    repswlen
    mpan2
    @1
    cvv
    wcel
    @2
    @3
    wb
    @0
    cS
    cc0
    creps
    ovex
    @1
    cvv
    hasheq0
    mp1i
    mpbid
end
