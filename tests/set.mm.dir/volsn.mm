include "cr.mm"
include "wcel.mm"
include "csn.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cc0.mm"
include "cdm.mm"
include "wceq.mm"
include "snmbl.mm"
include "mblvol.mm"
include "syl.mm"
include "ovolsn.mm"
include "eqtrd.mm"

theorem volsn
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. RR -> ( vol ` { A } ) = 0 )

  proof
    cA
    cr
    wcel
    #
    cA
    csn
    #
    cvol
    cfv
    #
    @1
    covol
    cfv
    #
    cc0
    @0
    @1
    cvol
    cdm
    wcel
    @2
    @3
    wceq
    cA
    snmbl
    @1
    mblvol
    syl
    cA
    ovolsn
    eqtrd
end
