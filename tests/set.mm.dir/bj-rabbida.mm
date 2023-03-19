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

theorem bj-rabbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume bj-rabbida.nf: |- F/ x ph
  assume bj-rabbida.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


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
    bj-rabbida.nf
    wph
    vx
    cv
    cA
    wcel
    @0
    bj-rabbida.1
    ex
    ralrimi
    wps
    wch
    vx
    cA
    rabbi
    sylib
end
