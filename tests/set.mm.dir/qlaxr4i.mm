include "cort.mm"
include "fveq2i.mm"

theorem qlaxr4i
  let cA: class A
  let cB: class B
  assume qlaxr4.1: |- A e. CH
  assume qlaxr4.2: |- B e. CH
  assume qlaxr4.3: |- A = B


  assert |- ( _|_ ` A ) = ( _|_ ` B )

  proof
    cA
    cB
    cort
    qlaxr4.3
    fveq2i
end
