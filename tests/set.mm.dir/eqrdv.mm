include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "alrimiv.mm"
include "dfcleq.mm"
include "sylibr.mm"

theorem eqrdv
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume eqrdv.1: |- ( ph -> ( x e. A <-> x e. B ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> A = B )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wb
    #
    vx
    wal
    cA
    cB
    wceq
    wph
    @1
    vx
    eqrdv.1
    alrimiv
    vx
    cA
    cB
    dfcleq
    sylibr
end
