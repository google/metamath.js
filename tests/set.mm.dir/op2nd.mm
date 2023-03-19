include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "2ndval.mm"
include "op2nda.mm"
include "eqtri.mm"

theorem op2nd
  let cA: class A
  let cB: class B
  assume op1st.1: |- A e. _V
  assume op1st.2: |- B e. _V


  assert |- ( 2nd ` <. A , B >. ) = B

  proof
    cA
    cB
    cop
    #
    c2nd
    cfv
    @0
    csn
    crn
    cuni
    cB
    @0
    2ndval
    cA
    cB
    op1st.1
    op1st.2
    op2nda
    eqtri
end
