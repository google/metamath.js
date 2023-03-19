include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wo.mm"
include "r19.9rzv.mm"
include "orbi1d.mm"
include "r19.43.mm"
include "syl6rbbr.mm"

theorem r19.45zv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ph x
  assert |- ( A =/= (/) -> ( E. x e. A ( ph \/ ps ) <-> ( ph \/ E. x e. A ps ) ) )

  proof
    cA
    c0
    wne
    #
    wph
    wps
    vx
    cA
    wrex
    #
    wo
    wph
    vx
    cA
    wrex
    #
    @1
    wo
    wph
    wps
    wo
    vx
    cA
    wrex
    @0
    wph
    @2
    @1
    wph
    vx
    cA
    r19.9rzv
    orbi1d
    wph
    wps
    vx
    cA
    r19.43
    syl6rbbr
end
