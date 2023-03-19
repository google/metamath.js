include "w3a.mm"
include "wral.mm"
include "wa.mm"
include "df-3an.mm"
include "ralbii.mm"
include "r19.26.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem r19.26-3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph /\ ps /\ ch ) <-> ( A. x e. A ph /\ A. x e. A ps /\ A. x e. A ch ) )

  proof
    wph
    wps
    wch
    w3a
    #
    vx
    cA
    wral
    wph
    wps
    wa
    #
    wch
    wa
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wral
    #
    wch
    vx
    cA
    wral
    #
    wa
    #
    wph
    vx
    cA
    wral
    #
    wps
    vx
    cA
    wral
    #
    @4
    w3a
    #
    @0
    @2
    vx
    cA
    wph
    wps
    wch
    df-3an
    ralbii
    @1
    wch
    vx
    cA
    r19.26
    @5
    @6
    @7
    wa
    #
    @4
    wa
    @8
    @3
    @9
    @4
    wph
    wps
    vx
    cA
    r19.26
    anbi1i
    @6
    @7
    @4
    df-3an
    bitr4i
    3bitri
end
