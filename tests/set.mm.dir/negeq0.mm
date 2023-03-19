include "cneg.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "neg0.mm"
include "eqeq2i.mm"
include "wb.mm"
include "0cn.mm"
include "neg11.mm"
include "mpan2.mm"
include "syl5rbbr.mm"

theorem negeq0
  let cA: class A


  assert |- ( A e. CC -> ( A = 0 <-> -u A = 0 ) )

  proof
    cA
    cneg
    #
    cc0
    wceq
    @0
    cc0
    cneg
    #
    wceq
    #
    cA
    cc
    wcel
    #
    cA
    cc0
    wceq
    #
    @1
    cc0
    @0
    neg0
    eqeq2i
    @3
    cc0
    cc
    wcel
    @2
    @4
    wb
    0cn
    cA
    cc0
    neg11
    mpan2
    syl5rbbr
end
