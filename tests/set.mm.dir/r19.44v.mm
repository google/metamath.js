include "wo.mm"
include "wrex.mm"
include "r19.43.mm"
include "id.mm"
include "rexlimivw.mm"
include "orim2i.mm"
include "sylbi.mm"

theorem r19.44v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ps x
  assert |- ( E. x e. A ( ph \/ ps ) -> ( E. x e. A ph \/ ps ) )

  proof
    wph
    wps
    wo
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    #
    wps
    vx
    cA
    wrex
    #
    wo
    @0
    wps
    wo
    wph
    wps
    vx
    cA
    r19.43
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
    orim2i
    sylbi
end
