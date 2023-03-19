include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "simpl.mm"
include "mul01d.mm"
include "wb.mm"
include "0cn.mm"
include "divmul.mm"
include "mp3an12.mm"
include "mpbird.mm"

theorem div0
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( 0 / A ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cc0
    cA
    cdiv
    co
    cc0
    wceq
    #
    cA
    cc0
    cmul
    co
    cc0
    wceq
    #
    @2
    cA
    @0
    @1
    simpl
    mul01d
    cc0
    cc
    wcel
    #
    @5
    @2
    @3
    @4
    wb
    0cn
    0cn
    cc0
    cc0
    cA
    divmul
    mp3an12
    mpbird
end
