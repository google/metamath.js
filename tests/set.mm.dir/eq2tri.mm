include "wceq.mm"
include "wa.mm"
include "ancom.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "3bitr3i.mm"

theorem eq2tri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume eq2tr.1: |- ( A = C -> D = F )
  assume eq2tr.2: |- ( B = D -> C = G )


  assert |- ( ( A = C /\ B = F ) <-> ( B = D /\ A = G ) )

  proof
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    @1
    @0
    wa
    @0
    cB
    cF
    wceq
    #
    wa
    @1
    cA
    cG
    wceq
    #
    wa
    @0
    @1
    ancom
    @0
    @1
    @2
    @0
    cD
    cF
    cB
    eq2tr.1
    eqeq2d
    pm5.32i
    @1
    @0
    @3
    @1
    cC
    cG
    cA
    eq2tr.2
    eqeq2d
    pm5.32i
    3bitr3i
end
