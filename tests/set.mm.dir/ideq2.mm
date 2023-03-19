include "cid.mm"
include "wbr.mm"
include "wcel.mm"
include "wceq.mm"
include "brid.mm"
include "ideqg.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "syl5bb.mm"

theorem ideq2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A _I B <-> A = B ) )

  proof
    cA
    cB
    cid
    wbr
    cB
    cA
    cid
    wbr
    #
    cA
    cV
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cB
    brid
    @1
    @0
    cB
    cA
    wceq
    @2
    cB
    cA
    cV
    ideqg
    cB
    cA
    eqcom
    syl6bb
    syl5bb
end
