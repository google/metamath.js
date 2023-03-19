include "cz.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "elfz1eq.mm"
include "elfz3.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "impbid2.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem fzsn
  let cM: class M
  let vk: setvar k
  let cN: class N
  let cK: class K


  assert |- ( M e. ZZ -> ( M ... M ) = { M } )

  proof
    cM
    cz
    wcel
    #
    vk
    cM
    cM
    cfz
    co
    #
    cM
    csn
    #
    @0
    vk
    cv
    #
    @1
    wcel
    #
    @3
    cM
    wceq
    #
    @3
    @2
    wcel
    @0
    @4
    @5
    @3
    cM
    elfz1eq
    @0
    @4
    @5
    cM
    @1
    wcel
    cM
    elfz3
    @3
    cM
    @1
    eleq1
    syl5ibrcom
    impbid2
    vk
    cM
    velsn
    syl6bbr
    eqrdv
end
