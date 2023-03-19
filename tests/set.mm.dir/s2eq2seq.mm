include "wcel.mm"
include "wa.mm"
include "cs2.mm"
include "wceq.mm"
include "cs1.mm"
include "s2eq2s1eq.mm"
include "wb.mm"
include "s111.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem s2eq2seq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( <" A B "> = <" C D "> <-> ( A = C /\ B = D ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    wa
    #
    cA
    cB
    cs2
    cC
    cD
    cs2
    wceq
    cA
    cs1
    cC
    cs1
    wceq
    #
    cB
    cs1
    cD
    cs1
    wceq
    #
    wa
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    cA
    cB
    cC
    cD
    cV
    s2eq2s1eq
    @4
    @5
    @7
    @6
    @8
    @0
    @2
    @5
    @7
    wb
    @1
    @3
    cV
    cA
    cC
    s111
    ad2ant2r
    @1
    @3
    @6
    @8
    wb
    @0
    @2
    cV
    cB
    cD
    s111
    ad2ant2l
    anbi12d
    bitrd
end
