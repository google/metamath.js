include "cfullfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "eqcom.mm"
include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "wb.mm"
include "fullfunfnv.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "fullfunfv.mm"
include "eqeq2i.mm"
include "3bitr3i.mm"

theorem brfullfun
  let cA: class A
  let cB: class B
  let cF: class F
  assume brfullfun.1: |- A e. _V
  assume brfullfun.2: |- B e. _V


  assert |- ( A FullFun F B <-> B = ( F ` A ) )

  proof
    cA
    cF
    cfullfn
    #
    cfv
    #
    cB
    wceq
    #
    cB
    @1
    wceq
    cA
    cB
    @0
    wbr
    #
    cB
    cA
    cF
    cfv
    #
    wceq
    @1
    cB
    eqcom
    @0
    cvv
    wfn
    cA
    cvv
    wcel
    @2
    @3
    wb
    cF
    fullfunfnv
    brfullfun.1
    cvv
    cA
    cB
    @0
    fnbrfvb
    mp2an
    @1
    @4
    cB
    cA
    cF
    fullfunfv
    eqeq2i
    3bitr3i
end
