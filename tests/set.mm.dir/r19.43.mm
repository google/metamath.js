include "wn.mm"
include "wi.mm"
include "wrex.mm"
include "wral.mm"
include "wo.mm"
include "r19.35.mm"
include "df-or.mm"
include "rexbii.mm"
include "ralnex.mm"
include "imbi1i.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem r19.43
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ( ph \/ ps ) <-> ( E. x e. A ph \/ E. x e. A ps ) )

  proof
    wph
    wn
    #
    wps
    wi
    #
    vx
    cA
    wrex
    @0
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
    #
    wph
    wps
    wo
    #
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    #
    @3
    wo
    #
    @0
    wps
    vx
    cA
    r19.35
    @5
    @1
    vx
    cA
    wph
    wps
    df-or
    rexbii
    @7
    @6
    wn
    #
    @3
    wi
    @4
    @6
    @3
    df-or
    @2
    @8
    @3
    wph
    vx
    cA
    ralnex
    imbi1i
    bitr4i
    3bitr4i
end
