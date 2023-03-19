include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "recid.mm"
include "mpan.mm"

theorem recidzi
  let cA: class A
  assume divclz.1: |- A e. CC


  assert |- ( A =/= 0 -> ( A x. ( 1 / A ) ) = 1 )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cA
    c1
    cA
    cdiv
    co
    cmul
    co
    c1
    wceq
    divclz.1
    cA
    recid
    mpan
end
