include "cr.mm"
include "wcel.mm"
include "csn.mm"
include "cfn.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "snfi.mm"
include "snssi.mm"
include "ovolfi.mm"
include "sylancr.mm"

theorem ovolsn
  let cA: class A


  assert |- ( A e. RR -> ( vol* ` { A } ) = 0 )

  proof
    cA
    cr
    wcel
    cA
    csn
    #
    cfn
    wcel
    @0
    cr
    wss
    @0
    covol
    cfv
    cc0
    wceq
    cA
    snfi
    cA
    cr
    snssi
    @0
    ovolfi
    sylancr
end
