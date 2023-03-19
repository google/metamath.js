include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wo.mm"
include "r19.9rzv.mm"
include "orbi2d.mm"
include "r19.43.mm"
include "syl6rbbr.mm"

theorem r19.44zv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ps x
  assert |- ( A =/= (/) -> ( E. x e. A ( ph \/ ps ) <-> ( E. x e. A ph \/ ps ) ) )

  proof
    cA
    c0
    wne
    #
    wph
    vx
    cA
    wrex
    #
    wps
    wo
    @1
    wps
    vx
    cA
    wrex
    #
    wo
    wph
    wps
    wo
    vx
    cA
    wrex
    @0
    wps
    @2
    @1
    wps
    vx
    cA
    r19.9rzv
    orbi2d
    wph
    wps
    vx
    cA
    r19.43
    syl6rbbr
end
