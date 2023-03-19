include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "bj-ceqsalgv.mm"
include "ax-mp.mm"

theorem bj-ceqsal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bj-ceqsal.1: |- F/ x ps
  assume bj-ceqsal.2: |- A e. _V
  assume bj-ceqsal.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A. x ( x = A -> ph ) <-> ps )

  proof
    cA
    cvv
    wcel
    vx
    cv
    cA
    wceq
    wph
    wi
    vx
    wal
    wps
    wb
    bj-ceqsal.2
    wph
    wps
    vx
    cA
    cvv
    bj-ceqsal.1
    bj-ceqsal.3
    bj-ceqsalgv
    ax-mp
end
