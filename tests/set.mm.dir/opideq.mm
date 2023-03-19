include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "opthg.mm"
include "anidms.mm"
include "anidm.mm"
include "syl6bb.mm"

theorem opideq
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( <. A , A >. = <. B , B >. <-> A = B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    cop
    cB
    cB
    cop
    wceq
    #
    cA
    cB
    wceq
    #
    @2
    wa
    #
    @2
    @0
    @1
    @3
    wb
    cA
    cA
    cB
    cB
    cV
    cV
    opthg
    anidms
    @2
    anidm
    syl6bb
end
