include "wi.mm"
include "wrex.mm"
include "wral.mm"
include "r19.35.mm"
include "id.mm"
include "rexlimivw.mm"
include "imim2i.mm"
include "sylbi.mm"

theorem r19.36v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ps x
  assert |- ( E. x e. A ( ph -> ps ) -> ( A. x e. A ph -> ps ) )

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
    @0
    wps
    wi
    wph
    wps
    vx
    cA
    r19.35
    @1
    wps
    @0
    wps
    wps
    vx
    cA
    wps
    id
    rexlimivw
    imim2i
    sylbi
end
