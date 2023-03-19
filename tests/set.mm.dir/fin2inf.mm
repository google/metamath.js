include "com.mm"
include "csdm.mm"
include "relsdom.mm"
include "brrelex2i.mm"

theorem fin2inf
  let cA: class A


  assert |- ( A ~< _om -> _om e. _V )

  proof
    cA
    com
    csdm
    relsdom
    brrelex2i
end
