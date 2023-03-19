include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "wmo.mm"
include "funopab.mm"
include "wi.mm"
include "moanimv.mm"
include "mpbir.mm"
include "mpgbir.mm"
include "dmopabss.mm"
include "ssexi.mm"
include "funex.mm"
include "mp2an.mm"

theorem opabex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume opabex.1: |- A e. _V
  assume opabex.2: |- ( x e. A -> E* y ph )

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- { <. x , y >. | ( x e. A /\ ph ) } e. _V

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    wfun
    #
    @2
    cdm
    #
    cvv
    wcel
    @2
    cvv
    wcel
    @3
    @1
    vy
    wmo
    #
    vx
    @1
    vx
    vy
    funopab
    @5
    @0
    wph
    vy
    wmo
    wi
    opabex.2
    @0
    wph
    vy
    moanimv
    mpbir
    mpgbir
    @4
    cA
    opabex.1
    wph
    vx
    vy
    cA
    dmopabss
    ssexi
    cvv
    @2
    funex
    mp2an
end
