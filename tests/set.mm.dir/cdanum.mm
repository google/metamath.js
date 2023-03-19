include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "con0.mm"
include "ccda.mm"
include "cen.mm"
include "wbr.mm"
include "cardon.mm"
include "oacl.mm"
include "mp2an.mm"
include "cardacda.mm"
include "ensymd.mm"
include "isnumi.mm"
include "sylancr.mm"

theorem cdanum
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( A +c B ) e. dom card )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @0
    wcel
    wa
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    coa
    co
    #
    con0
    wcel
    #
    @4
    cA
    cB
    ccda
    co
    #
    cen
    wbr
    @6
    @0
    wcel
    @2
    con0
    wcel
    @3
    con0
    wcel
    @5
    cA
    cardon
    cB
    cardon
    @2
    @3
    oacl
    mp2an
    @1
    @6
    @4
    cA
    cB
    cardacda
    ensymd
    @4
    @6
    isnumi
    sylancr
end
