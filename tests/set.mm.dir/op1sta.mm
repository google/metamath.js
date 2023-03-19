include "cop.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "dmsnop.mm"
include "unieqi.mm"
include "unisn.mm"
include "eqtri.mm"

theorem op1sta
  let cA: class A
  let cB: class B
  assume cnvsn.1: |- A e. _V
  assume cnvsn.2: |- B e. _V


  assert |- U. dom { <. A , B >. } = A

  proof
    cA
    cB
    cop
    csn
    cdm
    #
    cuni
    cA
    csn
    #
    cuni
    cA
    @0
    @1
    cA
    cB
    cnvsn.2
    dmsnop
    unieqi
    cA
    cnvsn.1
    unisn
    eqtri
end
