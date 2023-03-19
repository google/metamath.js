include "wb.mm"
include "wral.mm"
include "crab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabbi.mm"
include "sylib.mm"

theorem rabbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rabbida.1: |- F/ x ph
  assume rabbida.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> { x e. A | ps } = { x e. A | ch } )

  proof
    wph
    wps
    wch
    wb
    #
    vx
    cA
    wral
    wps
    vx
    cA
    crab
    wch
    vx
    cA
    crab
    wceq
    wph
    @0
    vx
    cA
    rabbida.1
    wph
    vx
    cv
    cA
    wcel
    @0
    rabbida.2
    ex
    ralrimi
    wps
    wch
    vx
    cA
    rabbi
    sylib
end
