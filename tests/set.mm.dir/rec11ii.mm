include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "rec11i.mm"
include "mp2an.mm"

theorem rec11ii
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divneq0.3: |- A =/= 0
  assume divneq0.4: |- B =/= 0


  assert |- ( ( 1 / A ) = ( 1 / B ) <-> A = B )

  proof
    cA
    cc0
    wne
    cB
    cc0
    wne
    c1
    cA
    cdiv
    co
    c1
    cB
    cdiv
    co
    wceq
    cA
    cB
    wceq
    wb
    divneq0.3
    divneq0.4
    cA
    cB
    divclz.1
    divclz.2
    rec11i
    mp2an
end
