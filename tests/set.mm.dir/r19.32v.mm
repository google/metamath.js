include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wo.mm"
include "r19.21v.mm"
include "df-or.mm"
include "ralbii.mm"
include "3bitr4i.mm"

theorem r19.32v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) )

  proof
    wph
    wn
    #
    wps
    wi
    #
    vx
    cA
    wral
    @0
    wps
    vx
    cA
    wral
    #
    wi
    wph
    wps
    wo
    #
    vx
    cA
    wral
    wph
    @2
    wo
    @0
    wps
    vx
    cA
    r19.21v
    @3
    @1
    vx
    cA
    wph
    wps
    df-or
    ralbii
    wph
    @2
    df-or
    3bitr4i
end
