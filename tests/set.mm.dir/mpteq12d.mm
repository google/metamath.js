include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "nfv.mm"
include "eleq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "opabbid.mm"
include "df-mpt.mm"
include "3eqtr4g.mm"

theorem mpteq12d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume mpteq12d.1: |- F/ x ph
  assume mpteq12d.3: |- ( ph -> A = C )
  assume mpteq12d.4: |- ( ph -> B = D )


  assert |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    @0
    cC
    wcel
    #
    @2
    cD
    wceq
    #
    wa
    #
    vx
    vy
    copab
    vx
    cA
    cB
    cmpt
    vx
    cC
    cD
    cmpt
    wph
    @4
    @7
    vx
    vy
    mpteq12d.1
    wph
    vy
    nfv
    wph
    @1
    @5
    @3
    @6
    wph
    cA
    cC
    @0
    mpteq12d.3
    eleq2d
    wph
    cB
    cD
    @2
    mpteq12d.4
    eqeq2d
    anbi12d
    opabbid
    vx
    vy
    cA
    cB
    df-mpt
    vx
    vy
    cC
    cD
    df-mpt
    3eqtr4g
end
