include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "cr.mm"
include "wss.mm"
include "wbr.mm"
include "mblss.mm"
include "ovolge0.mm"
include "syl.mm"
include "mblvol.mm"
include "breqtrrd.mm"

theorem volge0
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. dom vol -> 0 <_ ( vol ` A ) )

  proof
    cA
    cvol
    cdm
    wcel
    #
    cc0
    cA
    covol
    cfv
    #
    cA
    cvol
    cfv
    cle
    @0
    cA
    cr
    wss
    cc0
    @1
    cle
    wbr
    cA
    mblss
    cA
    ovolge0
    syl
    cA
    mblvol
    breqtrrd
end
