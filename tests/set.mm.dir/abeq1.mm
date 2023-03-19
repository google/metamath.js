include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "abeq2.mm"
include "eqcom.mm"
include "bicom.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem abeq1
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( { x | ph } = A <-> A. x ( ph <-> x e. A ) )

  proof
    cA
    wph
    vx
    cab
    #
    wceq
    vx
    cv
    cA
    wcel
    #
    wph
    wb
    #
    vx
    wal
    @0
    cA
    wceq
    wph
    @1
    wb
    #
    vx
    wal
    wph
    vx
    cA
    abeq2
    @0
    cA
    eqcom
    @3
    @2
    vx
    wph
    @1
    bicom
    albii
    3bitr4i
end
