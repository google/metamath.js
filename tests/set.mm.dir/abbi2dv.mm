include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "wceq.mm"
include "alrimiv.mm"
include "abeq2.mm"
include "sylibr.mm"

theorem abbi2dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume abbi2dv.1: |- ( ph -> ( x e. A <-> ps ) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> A = { x | ps } )

  proof
    wph
    vx
    cv
    cA
    wcel
    wps
    wb
    #
    vx
    wal
    cA
    wps
    vx
    cab
    wceq
    wph
    @0
    vx
    abbi2dv.1
    alrimiv
    wps
    vx
    cA
    abeq2
    sylibr
end
