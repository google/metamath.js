include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wex.mm"
include "rnopab.mm"
include "df-mpt.mm"
include "rneqi.mm"
include "df-rex.mm"
include "abbii.mm"
include "3eqtr4i.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "crab.mm"
include "eqid.mm"
include "dmmpt.mm"
include "rabexgfGS.mm"
include "syl5eqel.mm"
include "funex.mm"
include "sylancr.mm"
include "rnexg.mm"
include "3syl.mm"
include "syl5eqelr.mm"

theorem abrexexd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume abrexexd.0: |- F/_ x A
  assume abrexexd.1: |- ( ph -> A e. _V )

  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ph -> { y | E. x e. A y = B } e. _V )

  proof
    wph
    vy
    cv
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cvv
    vx
    cv
    cA
    wcel
    @0
    wa
    #
    vx
    vy
    copab
    #
    crn
    @5
    vx
    wex
    #
    vy
    cab
    @4
    @2
    @5
    vx
    vy
    rnopab
    @3
    @6
    vx
    vy
    cA
    cB
    df-mpt
    rneqi
    @1
    @7
    vy
    @0
    vx
    cA
    df-rex
    abbii
    3eqtr4i
    wph
    cA
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    abrexexd.1
    @8
    @3
    wfun
    @3
    cdm
    #
    cvv
    wcel
    @9
    vx
    cA
    cB
    funmpt
    @8
    @10
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    cvv
    vx
    cA
    cB
    @3
    @3
    eqid
    dmmpt
    @11
    vx
    cA
    cvv
    abrexexd.0
    rabexgfGS
    syl5eqel
    cvv
    @3
    funex
    sylancr
    @3
    cvv
    rnexg
    3syl
    syl5eqelr
end
