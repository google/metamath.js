include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "neg11.mm"
include "mp2an.mm"

theorem neg11i
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( -u A = -u B <-> A = B )

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
    cneg
    wceq
    cA
    cB
    wceq
    wb
    negidi.1
    pncan3i.2
    cA
    cB
    neg11
    mp2an
end
