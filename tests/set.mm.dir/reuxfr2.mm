include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wb.mm"
include "wtru.mm"
include "wcel.mm"
include "adantl.mm"
include "wrmo.mm"
include "reuxfr2d.mm"
include "trud.mm"

theorem reuxfr2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reuxfr2.1: |- ( y e. B -> A e. B )
  assume reuxfr2.2: |- ( x e. B -> E* y e. B x = A )

  disjoint ph x
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( E! x e. B E. y e. B ( x = A /\ ph ) <-> E! y e. B ph )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wa
    vy
    cB
    wrex
    vx
    cB
    wreu
    wph
    vy
    cB
    wreu
    wb
    wtru
    wph
    vx
    vy
    cA
    cB
    vy
    cv
    cB
    wcel
    cA
    cB
    wcel
    wtru
    reuxfr2.1
    adantl
    @0
    cB
    wcel
    @1
    vy
    cB
    wrmo
    wtru
    reuxfr2.2
    adantl
    reuxfr2d
    trud
end
