include "cop.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "rnsnop.mm"
include "unieqi.mm"
include "unisn.mm"
include "eqtri.mm"

theorem op2nda
  let cA: class A
  let cB: class B
  assume cnvsn.1: |- A e. _V
  assume cnvsn.2: |- B e. _V


  assert |- U. ran { <. A , B >. } = B

  proof
    cA
    cB
    cop
    csn
    crn
    #
    cuni
    cB
    csn
    #
    cuni
    cB
    @0
    @1
    cA
    cB
    cnvsn.1
    rnsnop
    unieqi
    cB
    cnvsn.2
    unisn
    eqtri
end
