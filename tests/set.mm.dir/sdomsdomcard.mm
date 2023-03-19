include "csdm.mm"
include "wbr.mm"
include "ccrd.mm"
include "cfv.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "numth3.mm"
include "cardid2.mm"
include "ensym.mm"
include "4syl.mm"
include "sdomentr.mm"
include "mpdan.mm"
include "sdomsdomcardi.mm"
include "impbii.mm"

theorem sdomsdomcard
  let cA: class A
  let cB: class B


  assert |- ( A ~< B <-> A ~< ( card ` B ) )

  proof
    cA
    cB
    csdm
    wbr
    #
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
    @1
    cen
    wbr
    #
    @2
    @0
    cB
    cvv
    wcel
    cB
    ccrd
    cdm
    wcel
    @1
    cB
    cen
    wbr
    @3
    cA
    cB
    csdm
    relsdom
    brrelex2i
    cB
    cvv
    numth3
    cB
    cardid2
    @1
    cB
    ensym
    4syl
    cA
    cB
    @1
    sdomentr
    mpdan
    cA
    cB
    sdomsdomcardi
    impbii
end
