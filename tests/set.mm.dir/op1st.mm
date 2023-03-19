include "cop.mm"
include "c1st.mm"
include "cfv.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "1stval.mm"
include "op1sta.mm"
include "eqtri.mm"

theorem op1st
  let cA: class A
  let cB: class B
  assume op1st.1: |- A e. _V
  assume op1st.2: |- B e. _V


  assert |- ( 1st ` <. A , B >. ) = A

  proof
    cA
    cB
    cop
    #
    c1st
    cfv
    @0
    csn
    cdm
    cuni
    cA
    @0
    1stval
    cA
    cB
    op1st.1
    op1st.2
    op1sta
    eqtri
end
