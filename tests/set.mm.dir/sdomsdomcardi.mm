include "ccrd.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "cen.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "c0.mm"
include "sdom0.mm"
include "ndmfv.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "cardid2.mm"
include "syl.mm"
include "sdomentr.mm"
include "mpdan.mm"

theorem sdomsdomcardi
  let cA: class A
  let cB: class B


  assert |- ( A ~< ( card ` B ) -> A ~< B )

  proof
    cA
    cB
    ccrd
    cfv
    #
    csdm
    wbr
    #
    @0
    cB
    cen
    wbr
    #
    cA
    cB
    csdm
    wbr
    @1
    cB
    ccrd
    cdm
    wcel
    #
    @2
    @3
    @1
    @3
    wn
    #
    @1
    cA
    c0
    csdm
    wbr
    cA
    sdom0
    @4
    @0
    c0
    cA
    csdm
    cB
    ccrd
    ndmfv
    breq2d
    mtbiri
    con4i
    cB
    cardid2
    syl
    cA
    @0
    cB
    sdomentr
    mpdan
end
