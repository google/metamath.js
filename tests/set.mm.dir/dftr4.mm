include "wtr.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "df-tr.mm"
include "sspwuni.mm"
include "bitr4i.mm"

theorem dftr4
  let cA: class A


  assert |- ( Tr A <-> A C_ ~P A )

  proof
    cA
    wtr
    cA
    cuni
    cA
    wss
    cA
    cA
    cpw
    wss
    cA
    df-tr
    cA
    cA
    sspwuni
    bitr4i
end
