include "cvv.mm"
include "wcel.mm"
include "wnfc.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "wb.mm"
include "csbiebt.mm"
include "mp2an.mm"

theorem csbieb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbieb.1: |- A e. _V
  assume csbieb.2: |- F/_ x C

  disjoint A x
  assert |- ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C )

  proof
    cA
    cvv
    wcel
    vx
    cC
    wnfc
    vx
    cv
    cA
    wceq
    cB
    cC
    wceq
    wi
    vx
    wal
    vx
    cA
    cB
    csb
    cC
    wceq
    wb
    csbieb.1
    csbieb.2
    vx
    cA
    cB
    cC
    cvv
    csbiebt
    mp2an
end
