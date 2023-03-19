include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "csdm.mm"
include "wne.mm"
include "wcel.mm"
include "peano1.mm"
include "infsdomnn.mm"
include "mpan2.mm"
include "cvv.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "0sdomg.mm"
include "syl.mm"
include "mpbid.mm"

theorem infn0
  let cA: class A


  assert |- ( _om ~<_ A -> A =/= (/) )

  proof
    com
    cA
    cdom
    wbr
    #
    c0
    cA
    csdm
    wbr
    #
    cA
    c0
    wne
    #
    @0
    c0
    com
    wcel
    @1
    peano1
    cA
    c0
    infsdomnn
    mpan2
    @0
    cA
    cvv
    wcel
    @1
    @2
    wb
    com
    cA
    cdom
    reldom
    brrelex2i
    cA
    cvv
    0sdomg
    syl
    mpbid
end
