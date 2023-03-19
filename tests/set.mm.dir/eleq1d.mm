include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "df-clel.mm"
include "3bitr4g.mm"

theorem eleq1d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  let vx: setvar x
  assume eleq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A e. C <-> B e. C ) )

  proof
    wph
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cC
    wcel
    #
    wa
    #
    vx
    wex
    @0
    cB
    wceq
    #
    @2
    wa
    #
    vx
    wex
    cA
    cC
    wcel
    cB
    cC
    wcel
    wph
    @3
    @5
    vx
    wph
    @1
    @4
    @2
    wph
    cA
    cB
    @0
    eleq1d.1
    eqeq2d
    anbi1d
    exbidv
    vx
    cA
    cC
    df-clel
    vx
    cB
    cC
    df-clel
    3bitr4g
end
