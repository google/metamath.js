include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "wtr.mm"
include "unipw.mm"
include "sseq1i.mm"
include "df-tr.mm"
include "dftr4.mm"
include "3bitr4ri.mm"

theorem pwtr
  let cA: class A


  assert |- ( Tr A <-> Tr ~P A )

  proof
    cA
    cpw
    #
    cuni
    #
    @0
    wss
    cA
    @0
    wss
    @0
    wtr
    cA
    wtr
    @1
    cA
    @0
    cA
    unipw
    sseq1i
    @0
    df-tr
    cA
    dftr4
    3bitr4ri
end
