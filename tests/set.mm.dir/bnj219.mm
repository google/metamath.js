include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "wel.mm"
include "cep.mm"
include "wbr.mm"
include "vex.mm"
include "bnj216.mm"
include "epel.mm"
include "sylibr.mm"

theorem bnj219
  let vm: setvar m
  let vn: setvar n


  assert |- ( n = suc m -> m _E n )

  proof
    vn
    cv
    #
    vm
    cv
    #
    csuc
    wceq
    vm
    vn
    wel
    @1
    @0
    cep
    wbr
    @0
    @1
    vm
    vex
    bnj216
    vm
    vn
    epel
    sylibr
end
