include "wreu.mm"
include "wb.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "adantl.mm"
include "wceq.mm"
include "reuxfrd.mm"
include "trud.mm"

theorem reuxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reuxfr.1: |- ( y e. B -> A e. B )
  assume reuxfr.2: |- ( x e. B -> E! y e. B x = A )
  assume reuxfr.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( E! x e. B ph <-> E! y e. B ps )

  proof
    wph
    vx
    cB
    wreu
    wps
    vy
    cB
    wreu
    wb
    wtru
    wph
    wps
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
    reuxfr.1
    adantl
    vx
    cv
    #
    cB
    wcel
    @0
    cA
    wceq
    vy
    cB
    wreu
    wtru
    reuxfr.2
    adantl
    reuxfr.3
    reuxfrd
    trud
end
