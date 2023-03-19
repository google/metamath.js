include "cop.mm"
include "csdm.mm"
include "wcel.mm"
include "cdom.mm"
include "cen.mm"
include "cdif.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "df-sdom.mm"
include "eleq2i.mm"
include "df-br.mm"
include "notbii.mm"
include "anbi12i.mm"
include "eldif.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem brsdom
  let cA: class A
  let cB: class B


  assert |- ( A ~< B <-> ( A ~<_ B /\ -. A ~~ B ) )

  proof
    cA
    cB
    cop
    #
    csdm
    wcel
    @0
    cdom
    cen
    cdif
    #
    wcel
    #
    cA
    cB
    csdm
    wbr
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wn
    #
    wa
    #
    csdm
    @1
    @0
    df-sdom
    eleq2i
    cA
    cB
    csdm
    df-br
    @6
    @0
    cdom
    wcel
    #
    @0
    cen
    wcel
    #
    wn
    #
    wa
    @2
    @3
    @7
    @5
    @9
    cA
    cB
    cdom
    df-br
    @4
    @8
    cA
    cB
    cen
    df-br
    notbii
    anbi12i
    @0
    cdom
    cen
    eldif
    bitr4i
    3bitr4i
end
