include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "cuz.mm"
include "cfv.mm"
include "wb.mm"
include "uzid.mm"
include "elfzp1.mm"
include "syl.mm"
include "csn.mm"
include "fzsn.mm"
include "eleq2d.mm"
include "velsn.mm"
include "syl6bb.mm"
include "orbi1d.mm"
include "bitrd.mm"
include "vex.mm"
include "elpr.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem fzpr
  let cM: class M
  let vm: setvar m


  assert |- ( M e. ZZ -> ( M ... ( M + 1 ) ) = { M , ( M + 1 ) } )

  proof
    cM
    cz
    wcel
    #
    vm
    cM
    cM
    c1
    caddc
    co
    #
    cfz
    co
    #
    cM
    @1
    cpr
    #
    @0
    vm
    cv
    #
    @2
    wcel
    #
    @4
    cM
    wceq
    #
    @4
    @1
    wceq
    #
    wo
    #
    @4
    @3
    wcel
    @0
    @5
    @4
    cM
    cM
    cfz
    co
    #
    wcel
    #
    @7
    wo
    #
    @8
    @0
    cM
    cM
    cuz
    cfv
    wcel
    @5
    @11
    wb
    cM
    uzid
    @4
    cM
    cM
    elfzp1
    syl
    @0
    @10
    @6
    @7
    @0
    @10
    @4
    cM
    csn
    #
    wcel
    @6
    @0
    @9
    @12
    @4
    cM
    fzsn
    eleq2d
    vm
    cM
    velsn
    syl6bb
    orbi1d
    bitrd
    @4
    cM
    @1
    vm
    vex
    elpr
    syl6bbr
    eqrdv
end
