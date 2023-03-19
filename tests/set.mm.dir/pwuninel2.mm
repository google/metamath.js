include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "pwnss.mm"
include "elssuni.mm"
include "nsyl.mm"

theorem pwuninel2
  let cA: class A
  let cV: class V


  assert |- ( U. A e. V -> -. ~P U. A e. A )

  proof
    cA
    cuni
    #
    cV
    wcel
    @0
    cpw
    #
    @0
    wss
    @1
    cA
    wcel
    @0
    cV
    pwnss
    @1
    cA
    elssuni
    nsyl
end
