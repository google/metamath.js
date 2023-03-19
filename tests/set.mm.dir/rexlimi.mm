include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "rgen.mm"
include "r19.23.mm"
include "mpbi.mm"

theorem rexlimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rexlimi.1: |- F/ x ps
  assume rexlimi.2: |- ( x e. A -> ( ph -> ps ) )


  assert |- ( E. x e. A ph -> ps )

  proof
    wph
    wps
    wi
    #
    vx
    cA
    wral
    wph
    vx
    cA
    wrex
    wps
    wi
    @0
    vx
    cA
    rexlimi.2
    rgen
    wph
    wps
    vx
    cA
    rexlimi.1
    r19.23
    mpbi
end
