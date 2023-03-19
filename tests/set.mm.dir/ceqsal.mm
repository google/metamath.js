include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "ceqsalg.mm"
include "ax-mp.mm"

theorem ceqsal
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ceqsal.1: |- F/ x ps
  assume ceqsal.2: |- A e. _V
  assume ceqsal.3: |- ( x = A -> ( ph <-> ps ) )

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
    ceqsal.2
    wph
    wps
    vx
    cA
    cvv
    ceqsal.1
    ceqsal.3
    ceqsalg
    ax-mp
end
