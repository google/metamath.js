include "eqtri.mm"

theorem qlaxr2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume qlaxr2.1: |- A e. CH
  assume qlaxr2.2: |- B e. CH
  assume qlaxr2.3: |- C e. CH
  assume qlaxr2.4: |- A = B
  assume qlaxr2.5: |- B = C


  assert |- A = C

  proof
    cA
    cB
    cC
    qlaxr2.4
    qlaxr2.5
    eqtri
end
