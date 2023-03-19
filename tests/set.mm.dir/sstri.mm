include "wss.mm"
include "sstr2.mm"
include "mp2.mm"

theorem sstri
  let cA: class A
  let cB: class B
  let cC: class C
  assume sstri.1: |- A C_ B
  assume sstri.2: |- B C_ C


  assert |- A C_ C

  proof
    cA
    cB
    wss
    cB
    cC
    wss
    cA
    cC
    wss
    sstri.1
    sstri.2
    cA
    cB
    cC
    sstr2
    mp2
end
