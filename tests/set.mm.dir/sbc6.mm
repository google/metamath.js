include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "sbc6g.mm"
include "ax-mp.mm"

theorem sbc6
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume sbc6.1: |- A e. _V

  disjoint A x
  assert |- ( [. A / x ]. ph <-> A. x ( x = A -> ph ) )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    wsbc
    vx
    cv
    cA
    wceq
    wph
    wi
    vx
    wal
    wb
    sbc6.1
    wph
    vx
    cA
    cvv
    sbc6g
    ax-mp
end
