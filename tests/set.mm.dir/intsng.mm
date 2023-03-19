include "wcel.mm"
include "csn.mm"
include "cint.mm"
include "cpr.mm"
include "dfsn2.mm"
include "inteqi.mm"
include "cin.mm"
include "wceq.mm"
include "intprg.mm"
include "anidms.mm"
include "inidm.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem intsng
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> |^| { A } = A )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    cint
    cA
    cA
    cpr
    #
    cint
    #
    cA
    @1
    @2
    cA
    dfsn2
    inteqi
    @0
    @3
    cA
    cA
    cin
    #
    cA
    @0
    @3
    @4
    wceq
    cA
    cA
    cV
    cV
    intprg
    anidms
    cA
    inidm
    syl6eq
    syl5eq
end
