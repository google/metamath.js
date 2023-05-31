include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "exbidv.mm"
include "df-rex.mm"
include "3bitr4g.mm"

theorem rexbidv2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume rexbidv2.1: |- ( ph -> ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    wps
    wa
    #
    vx
    wex
    @0
    cB
    wcel
    wch
    wa
    #
    vx
    wex
    wps
    vx
    cA
    wrex
    wch
    vx
    cB
    wrex
    wph
    @1
    @2
    vx
    rexbidv2.1
    exbidv
    wps
    vx
    cA
    df-rex
    wch
    vx
    cB
    df-rex
    3bitr4g
end
