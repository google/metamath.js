include "chj.mm"
include "oveq1i.mm"

theorem qlaxr5i
  let cA: class A
  let cB: class B
  let cC: class C
  assume qlaxr5.1: |- A e. CH
  assume qlaxr5.2: |- B e. CH
  assume qlaxr5.3: |- C e. CH
  assume qlaxr5.4: |- A = B


  assert |- ( A vH C ) = ( B vH C )

  proof
    cA
    cB
    cC
    chj
    qlaxr5.4
    oveq1i
end
