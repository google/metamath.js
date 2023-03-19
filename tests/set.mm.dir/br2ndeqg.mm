include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "op2ndg.mm"
include "eqeq1d.mm"
include "cvv.mm"
include "wfn.mm"
include "wb.mm"
include "wfo.mm"
include "fo2nd.mm"
include "fofn.mm"
include "ax-mp.mm"
include "opex.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "eqcom.mm"
include "3bitr3g.mm"

theorem br2ndeqg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. 2nd C <-> C = B ) )

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
    c2nd
    cfv
    #
    cC
    wceq
    #
    cB
    cC
    wceq
    @1
    cC
    c2nd
    wbr
    #
    cC
    cB
    wceq
    @0
    @2
    cB
    cC
    cA
    cB
    cV
    cW
    op2ndg
    eqeq1d
    c2nd
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
    c2nd
    wfo
    @5
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    cA
    cB
    opex
    cvv
    @1
    cC
    c2nd
    fnbrfvb
    mp2an
    cB
    cC
    eqcom
    3bitr3g
end
