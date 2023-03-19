include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "negcon1.mm"
include "mp2an.mm"

theorem negcon1i
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( -u A = B <-> -u B = A )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cneg
    cB
    wceq
    cB
    cneg
    cA
    wceq
    wb
    negidi.1
    pncan3i.2
    cA
    cB
    negcon1
    mp2an
end
