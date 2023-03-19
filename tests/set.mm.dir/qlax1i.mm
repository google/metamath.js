include "cort.mm"
include "cfv.mm"
include "ococi.mm"
include "eqcomi.mm"

theorem qlax1i
  let cA: class A
  assume qlax1.1: |- A e. CH


  assert |- A = ( _|_ ` ( _|_ ` A ) )

  proof
    cA
    cort
    cfv
    cort
    cfv
    cA
    cA
    qlax1.1
    ococi
    eqcomi
end
