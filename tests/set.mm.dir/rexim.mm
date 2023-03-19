include "wi.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "con3.mm"
include "ral2imi.mm"
include "con3d.mm"
include "dfrex2.mm"
include "3imtr4g.mm"

theorem rexim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph -> ps ) -> ( E. x e. A ph -> E. x e. A ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    cA
    wral
    #
    wph
    wn
    #
    vx
    cA
    wral
    #
    wn
    wps
    wn
    #
    vx
    cA
    wral
    #
    wn
    wph
    vx
    cA
    wrex
    wps
    vx
    cA
    wrex
    @1
    @5
    @3
    @0
    @4
    @2
    vx
    cA
    wph
    wps
    con3
    ral2imi
    con3d
    wph
    vx
    cA
    dfrex2
    wps
    vx
    cA
    dfrex2
    3imtr4g
end
