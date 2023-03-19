include "csuc.mm"
include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "noel.mm"
include "sucidg.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "mtoi.mm"
include "0ex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "con3i.mm"
include "sucprc.mm"
include "eqeq1d.mm"
include "mtbird.mm"
include "pm2.61i.mm"
include "neir.mm"

theorem nsuceq0
  let cA: class A


  assert |- suc A =/= (/)

  proof
    cA
    csuc
    #
    c0
    cA
    cvv
    wcel
    #
    @0
    c0
    wceq
    #
    wn
    @1
    @2
    cA
    c0
    wcel
    #
    cA
    noel
    @1
    cA
    @0
    wcel
    @2
    @3
    cA
    cvv
    sucidg
    @0
    c0
    cA
    eleq2
    syl5ibcom
    mtoi
    @1
    wn
    #
    @2
    cA
    c0
    wceq
    #
    @5
    @1
    @5
    @1
    c0
    cvv
    wcel
    0ex
    cA
    c0
    cvv
    eleq1
    mpbiri
    con3i
    @4
    @0
    cA
    c0
    cA
    sucprc
    eqeq1d
    mtbird
    pm2.61i
    neir
end
