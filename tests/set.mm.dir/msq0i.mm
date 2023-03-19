include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "mul0or.mm"
include "mp2an.mm"
include "oridm.mm"
include "bitri.mm"

theorem msq0i
  let cA: class A
  assume mul0or.1: |- A e. CC


  assert |- ( ( A x. A ) = 0 <-> A = 0 )

  proof
    cA
    cA
    cmul
    co
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    @1
    wo
    #
    @1
    cA
    cc
    wcel
    #
    @3
    @0
    @2
    wb
    mul0or.1
    mul0or.1
    cA
    cA
    mul0or
    mp2an
    @1
    oridm
    bitri
end
