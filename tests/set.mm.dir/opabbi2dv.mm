include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "copab.mm"
include "wrel.mm"
include "wceq.mm"
include "opabid2.mm"
include "ax-mp.mm"
include "opabbidv.mm"
include "syl5eqr.mm"

theorem opabbi2dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume opabbi2dv.1: |- Rel A
  assume opabbi2dv.3: |- ( ph -> ( <. x , y >. e. A <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A = { <. x , y >. | ps } )

  proof
    wph
    cA
    vx
    cv
    vy
    cv
    cop
    cA
    wcel
    #
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    cA
    wrel
    @1
    cA
    wceq
    opabbi2dv.1
    vx
    vy
    cA
    opabid2
    ax-mp
    wph
    @0
    wps
    vx
    vy
    opabbi2dv.3
    opabbidv
    syl5eqr
end
