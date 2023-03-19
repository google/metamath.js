include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cio.mm"
include "csn.mm"
include "crab.mm"
include "crio.mm"
include "weu.mm"
include "wceq.mm"
include "df-reu.mm"
include "sniota.mm"
include "sylbi.mm"
include "df-rab.mm"
include "df-riota.mm"
include "sneqi.mm"
include "3eqtr4g.mm"

theorem snriota
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E! x e. A ph -> { x e. A | ph } = { ( iota_ x e. A ph ) } )

  proof
    wph
    vx
    cA
    wreu
    #
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cab
    #
    @1
    vx
    cio
    #
    csn
    #
    wph
    vx
    cA
    crab
    wph
    vx
    cA
    crio
    #
    csn
    @0
    @1
    vx
    weu
    @2
    @4
    wceq
    wph
    vx
    cA
    df-reu
    @1
    vx
    sniota
    sylbi
    wph
    vx
    cA
    df-rab
    @5
    @3
    wph
    vx
    cA
    df-riota
    sneqi
    3eqtr4g
end
