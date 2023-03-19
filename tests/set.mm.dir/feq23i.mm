include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "feq23.mm"
include "mp2an.mm"

theorem feq23i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume feq23i.1: |- A = C
  assume feq23i.2: |- B = D


  assert |- ( F : A --> B <-> F : C --> D )

  proof
    cA
    cC
    wceq
    cB
    cD
    wceq
    cA
    cB
    cF
    wf
    cC
    cD
    cF
    wf
    wb
    feq23i.1
    feq23i.2
    cA
    cB
    cC
    cD
    cF
    feq23
    mp2an
end
