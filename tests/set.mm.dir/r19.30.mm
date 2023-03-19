include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wo.mm"
include "wrex.mm"
include "ralim.mm"
include "orcom.mm"
include "df-or.mm"
include "bitri.mm"
include "ralbii.mm"
include "dfrex2.mm"
include "orbi2i.mm"
include "imor.mm"
include "3bitr4i.mm"
include "3imtr4i.mm"

theorem r19.30
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph \/ ps ) -> ( A. x e. A ph \/ E. x e. A ps ) )

  proof
    wps
    wn
    #
    wph
    wi
    #
    vx
    cA
    wral
    @0
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wral
    #
    wi
    #
    wph
    wps
    wo
    #
    vx
    cA
    wral
    @3
    wps
    vx
    cA
    wrex
    #
    wo
    #
    @0
    wph
    vx
    cA
    ralim
    @5
    @1
    vx
    cA
    @5
    wps
    wph
    wo
    @1
    wph
    wps
    orcom
    wps
    wph
    df-or
    bitri
    ralbii
    @3
    @2
    wn
    #
    wo
    @8
    @3
    wo
    @7
    @4
    @3
    @8
    orcom
    @6
    @8
    @3
    wps
    vx
    cA
    dfrex2
    orbi2i
    @2
    @3
    imor
    3bitr4i
    3imtr4i
end
