include "cop.mm"
include "csdm.mm"
include "wcel.mm"
include "cdom.mm"
include "ccnv.mm"
include "cdif.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "dfsdom2.mm"
include "eleq2i.mm"
include "df-br.mm"
include "opelcnv.mm"
include "bitr4i.mm"
include "notbii.mm"
include "anbi12i.mm"
include "eldif.mm"
include "3bitr4i.mm"

theorem brsdom2
  let cA: class A
  let cB: class B
  assume brsdom2.1: |- A e. _V
  assume brsdom2.2: |- B e. _V


  assert |- ( A ~< B <-> ( A ~<_ B /\ -. B ~<_ A ) )

  proof
    cA
    cB
    cop
    #
    csdm
    wcel
    @0
    cdom
    cdom
    ccnv
    #
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
    cB
    cA
    cdom
    wbr
    #
    wn
    #
    wa
    #
    csdm
    @2
    @0
    dfsdom2
    eleq2i
    cA
    cB
    csdm
    df-br
    @7
    @0
    cdom
    wcel
    #
    @0
    @1
    wcel
    #
    wn
    #
    wa
    @3
    @4
    @8
    @6
    @10
    cA
    cB
    cdom
    df-br
    @5
    @9
    @5
    cB
    cA
    cop
    cdom
    wcel
    @9
    cB
    cA
    cdom
    df-br
    cA
    cB
    cdom
    brsdom2.1
    brsdom2.2
    opelcnv
    bitr4i
    notbii
    anbi12i
    @0
    cdom
    @1
    eldif
    bitr4i
    3bitr4i
end
