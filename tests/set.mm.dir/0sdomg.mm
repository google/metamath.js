include "wcel.mm"
include "c0.mm"
include "csdm.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "wne.mm"
include "cdom.mm"
include "wb.mm"
include "0domg.mm"
include "brsdom.mm"
include "baib.mm"
include "syl.mm"
include "wceq.mm"
include "ensymb.mm"
include "en0.mm"
include "bitri.mm"
include "necon3bbii.mm"
include "syl6bb.mm"

theorem 0sdomg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( (/) ~< A <-> A =/= (/) ) )

  proof
    cA
    cV
    wcel
    #
    c0
    cA
    csdm
    wbr
    #
    c0
    cA
    cen
    wbr
    #
    wn
    #
    cA
    c0
    wne
    @0
    c0
    cA
    cdom
    wbr
    #
    @1
    @3
    wb
    cA
    cV
    0domg
    @1
    @4
    @3
    c0
    cA
    brsdom
    baib
    syl
    @2
    cA
    c0
    @2
    cA
    c0
    cen
    wbr
    cA
    c0
    wceq
    c0
    cA
    ensymb
    cA
    en0
    bitri
    necon3bbii
    syl6bb
end
