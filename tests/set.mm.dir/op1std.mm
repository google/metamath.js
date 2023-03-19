include "cop.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "fveq2.mm"
include "op1st.mm"
include "syl6eq.mm"

theorem op1std
  let cA: class A
  let cB: class B
  let cC: class C
  assume op1st.1: |- A e. _V
  assume op1st.2: |- B e. _V


  assert |- ( C = <. A , B >. -> ( 1st ` C ) = A )

  proof
    cC
    cA
    cB
    cop
    #
    wceq
    cC
    c1st
    cfv
    @0
    c1st
    cfv
    cA
    cC
    @0
    c1st
    fveq2
    cA
    cB
    op1st.1
    op1st.2
    op1st
    syl6eq
end
