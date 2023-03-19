include "cop.mm"
include "cdom.mm"
include "wcel.mm"
include "csdm.mm"
include "cen.mm"
include "cun.mm"
include "wbr.mm"
include "wo.mm"
include "dfdom2.mm"
include "eleq2i.mm"
include "df-br.mm"
include "orbi12i.mm"
include "elun.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem brdom2
  let cA: class A
  let cB: class B


  assert |- ( A ~<_ B <-> ( A ~< B \/ A ~~ B ) )

  proof
    cA
    cB
    cop
    #
    cdom
    wcel
    @0
    csdm
    cen
    cun
    #
    wcel
    #
    cA
    cB
    cdom
    wbr
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wo
    #
    cdom
    @1
    @0
    dfdom2
    eleq2i
    cA
    cB
    cdom
    df-br
    @5
    @0
    csdm
    wcel
    #
    @0
    cen
    wcel
    #
    wo
    @2
    @3
    @6
    @4
    @7
    cA
    cB
    csdm
    df-br
    cA
    cB
    cen
    df-br
    orbi12i
    @0
    csdm
    cen
    elun
    bitr4i
    3bitr4i
end
