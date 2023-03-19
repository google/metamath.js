include "c0.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cen.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelexi.mm"
include "0domg.mm"
include "syl.mm"
include "pm4.71i.mm"
include "sbthb.mm"
include "en0.mm"
include "3bitri.mm"

theorem dom0
  let cA: class A


  assert |- ( A ~<_ (/) <-> A = (/) )

  proof
    cA
    c0
    cdom
    wbr
    #
    @0
    c0
    cA
    cdom
    wbr
    #
    wa
    cA
    c0
    cen
    wbr
    cA
    c0
    wceq
    @0
    @1
    @0
    cA
    cvv
    wcel
    @1
    cA
    c0
    cdom
    reldom
    brrelexi
    cA
    cvv
    0domg
    syl
    pm4.71i
    cA
    c0
    sbthb
    cA
    en0
    3bitri
end
