include "wi.mm"
include "wrex.mm"
include "wral.mm"
include "r19.35.mm"
include "cv.mm"
include "wcel.mm"
include "ax-1.mm"
include "ralrimi.mm"
include "imim1i.mm"
include "sylbi.mm"

theorem r19.37
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.37.1: |- F/ x ph


  assert |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) )

  proof
    wph
    wps
    wi
    vx
    cA
    wrex
    wph
    vx
    cA
    wral
    #
    wps
    vx
    cA
    wrex
    #
    wi
    wph
    @1
    wi
    wph
    wps
    vx
    cA
    r19.35
    wph
    @0
    @1
    wph
    wph
    vx
    cA
    r19.37.1
    wph
    vx
    cv
    cA
    wcel
    ax-1
    ralrimi
    imim1i
    sylbi
end
