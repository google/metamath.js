include "wss.mm"
include "wa.mm"
include "cin.mm"
include "pm3.2i.mm"
include "ssin.mm"
include "mpbi.mm"

theorem ssini
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssini.1: |- A C_ B
  assume ssini.2: |- A C_ C


  assert |- A C_ ( B i^i C )

  proof
    cA
    cB
    wss
    #
    cA
    cC
    wss
    #
    wa
    cA
    cB
    cC
    cin
    wss
    @0
    @1
    ssini.1
    ssini.2
    pm3.2i
    cA
    cB
    cC
    ssin
    mpbi
end
