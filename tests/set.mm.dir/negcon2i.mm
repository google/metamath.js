include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "negcon2.mm"
include "mp2an.mm"

theorem negcon2i
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( A = -u B <-> B = -u A )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cneg
    wceq
    cB
    cA
    cneg
    wceq
    wb
    negidi.1
    pncan3i.2
    cA
    cB
    negcon2
    mp2an
end
