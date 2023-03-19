include "nfcv.mm"
include "cbvcsb.mm"

theorem cbvcsbv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume cbvcsbv.1: |- ( x = y -> B = C )

  disjoint x y
  disjoint B y
  disjoint C x
  assert |- [_ A / x ]_ B = [_ A / y ]_ C

  proof
    vx
    vy
    cA
    cB
    cC
    vy
    cB
    nfcv
    vx
    cC
    nfcv
    cbvcsbv.1
    cbvcsb
end
