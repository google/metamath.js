include "crab.mm"
include "wceq.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "a1i.mm"
include "rabbidva2.mm"
include "trud.mm"

theorem rabbia2
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabbia2.1: |- ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) )


  assert |- { x e. A | ps } = { x e. B | ch }

  proof
    wps
    vx
    cA
    crab
    wch
    vx
    cB
    crab
    wceq
    wtru
    wps
    wch
    vx
    cA
    cB
    vx
    cv
    #
    cA
    wcel
    wps
    wa
    @0
    cB
    wcel
    wch
    wa
    wb
    wtru
    rabbia2.1
    a1i
    rabbidva2
    trud
end
