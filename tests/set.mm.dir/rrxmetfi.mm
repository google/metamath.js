include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cme.mm"
include "cfv.mm"
include "eqid.mm"
include "rrxmet.mm"
include "crrx.mm"
include "cbs.mm"
include "rrxbase.mm"
include "eqcomd.mm"
include "id.mm"
include "rrxbasefi.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleqtrd.mm"

theorem rrxmetfi
  let cD: class D
  let cI: class I
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  assume rrxmetfi.1: |- D = ( dist ` ( RR^ ` I ) )


  assert |- ( I e. Fin -> D e. ( Met ` ( RR ^m I ) ) )

  proof
    cI
    cfn
    wcel
    #
    cD
    vh
    cv
    cc0
    cfsupp
    wbr
    vh
    cr
    cI
    cmap
    co
    #
    crab
    #
    cme
    cfv
    @1
    cme
    cfv
    cD
    vh
    cI
    cfn
    @2
    @2
    eqid
    rrxmetfi.1
    rrxmet
    @0
    @2
    @1
    cme
    @0
    @2
    cI
    crrx
    cfv
    #
    cbs
    cfv
    #
    @1
    @0
    @4
    @2
    @4
    vh
    @3
    cI
    cfn
    @3
    eqid
    #
    @4
    eqid
    #
    rrxbase
    eqcomd
    @0
    @4
    @3
    cI
    @0
    id
    @5
    @6
    rrxbasefi
    eqtrd
    fveq2d
    eleqtrd
end
