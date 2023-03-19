include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cun.mm"
include "uniun.mm"
include "undif1.mm"
include "uncom.mm"
include "eqtr2i.mm"
include "unieqi.mm"
include "0ex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtr4ri.mm"
include "uneq1i.mm"
include "3eqtri.mm"

theorem unidif0
  let cA: class A


  assert |- U. ( A \ { (/) } ) = U. A

  proof
    cA
    c0
    csn
    #
    cdif
    #
    cuni
    #
    c0
    cA
    cuni
    #
    cun
    #
    @3
    c0
    cun
    @3
    @2
    @0
    cA
    cun
    #
    cuni
    #
    @0
    cuni
    #
    @3
    cun
    @4
    @1
    @0
    cun
    #
    cuni
    @2
    @7
    cun
    #
    @6
    @2
    @1
    @0
    uniun
    @5
    @8
    @8
    cA
    @0
    cun
    @5
    cA
    @0
    undif1
    cA
    @0
    uncom
    eqtr2i
    unieqi
    @9
    @2
    c0
    cun
    @2
    @7
    c0
    @2
    c0
    0ex
    unisn
    #
    uneq2i
    @2
    un0
    eqtr2i
    3eqtr4ri
    @0
    cA
    uniun
    @7
    c0
    @3
    @10
    uneq1i
    3eqtri
    c0
    @3
    uncom
    @3
    un0
    3eqtri
end
