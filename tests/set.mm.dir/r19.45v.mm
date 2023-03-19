include "wo.mm"
include "wrex.mm"
include "r19.43.mm"
include "id.mm"
include "rexlimivw.mm"
include "orim1i.mm"
include "sylbi.mm"

theorem r19.45v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( E. x e. A ( ph \/ ps ) -> ( ph \/ E. x e. A ps ) )

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
    wph
    @1
    wo
    wph
    wps
    vx
    cA
    r19.43
    @0
    wph
    @1
    wph
    wph
    vx
    cA
    wph
    id
    rexlimivw
    orim1i
    sylbi
end
