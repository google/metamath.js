include "eqcomi.mm"

theorem qlaxr1i
  let cA: class A
  let cB: class B
  assume qlaxr1.1: |- A e. CH
  assume qlaxr1.2: |- B e. CH
  assume qlaxr1.3: |- A = B


  assert |- B = A

  proof
    cA
    cB
    qlaxr1.3
    eqcomi
end
