include "cop.mm"
include "wceq.mm"
include "c2nd.mm"
include "cfv.mm"
include "fveq2.mm"
include "op2nd.mm"
include "syl6eq.mm"

theorem op2ndd
  let cA: class A
  let cB: class B
  let cC: class C
  assume op1st.1: |- A e. _V
  assume op1st.2: |- B e. _V


  assert |- ( C = <. A , B >. -> ( 2nd ` C ) = B )

  proof
    cC
    cA
    cB
    cop
    #
    wceq
    cC
    c2nd
    cfv
    @0
    c2nd
    cfv
    cB
    cC
    @0
    c2nd
    fveq2
    cA
    cB
    op1st.1
    op1st.2
    op2nd
    syl6eq
end
