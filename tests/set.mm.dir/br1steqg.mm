include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "op1stg.mm"
include "eqeq1d.mm"
include "cvv.mm"
include "wfn.mm"
include "wb.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "opex.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "eqcom.mm"
include "3bitr3g.mm"

theorem br1steqg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. 1st C <-> C = A ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cB
    cop
    #
    c1st
    cfv
    #
    cC
    wceq
    #
    cA
    cC
    wceq
    @1
    cC
    c1st
    wbr
    #
    cC
    cA
    wceq
    @0
    @2
    cA
    cC
    cA
    cB
    cV
    cW
    op1stg
    eqeq1d
    c1st
    cvv
    wfn
    #
    @1
    cvv
    wcel
    @3
    @4
    wb
    cvv
    cvv
    c1st
    wfo
    @5
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    cA
    cB
    opex
    cvv
    @1
    cC
    c1st
    fnbrfvb
    mp2an
    cA
    cC
    eqcom
    3bitr3g
end
