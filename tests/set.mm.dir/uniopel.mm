include "cop.mm"
include "wcel.mm"
include "cuni.mm"
include "cpr.mm"
include "uniop.mm"
include "opi2.mm"
include "eqeltri.mm"
include "elssuni.mm"
include "sseld.mm"
include "mpi.mm"

theorem uniopel
  let cA: class A
  let cB: class B
  let cC: class C
  assume opthw.1: |- A e. _V
  assume opthw.2: |- B e. _V


  assert |- ( <. A , B >. e. C -> U. <. A , B >. e. U. C )

  proof
    cA
    cB
    cop
    #
    cC
    wcel
    #
    @0
    cuni
    #
    @0
    wcel
    @2
    cC
    cuni
    #
    wcel
    @2
    cA
    cB
    cpr
    @0
    cA
    cB
    opthw.1
    opthw.2
    uniop
    cA
    cB
    opthw.1
    opthw.2
    opi2
    eqeltri
    @1
    @0
    @3
    @2
    @0
    cC
    elssuni
    sseld
    mpi
end
