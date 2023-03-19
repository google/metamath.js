include "c0.mm"
include "cpw.mm"
include "0elpw.mm"
include "ne0ii.mm"

theorem pwne0
  let cA: class A


  assert |- ~P A =/= (/)

  proof
    c0
    cA
    cpw
    cA
    0elpw
    ne0ii
end
