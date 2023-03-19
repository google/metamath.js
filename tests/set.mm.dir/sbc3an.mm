include "w3a.mm"
include "wsbc.mm"
include "wa.mm"
include "df-3an.mm"
include "sbcbii.mm"
include "sbcan.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "bitr4i.mm"

theorem sbc3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A


  assert |- ( [. A / x ]. ( ph /\ ps /\ ch ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps /\ [. A / x ]. ch ) )

  proof
    wph
    wps
    wch
    w3a
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wa
    #
    wch
    vx
    cA
    wsbc
    #
    wa
    #
    @2
    @3
    @5
    w3a
    @1
    wph
    wps
    wa
    #
    wch
    wa
    #
    vx
    cA
    wsbc
    @7
    vx
    cA
    wsbc
    #
    @5
    wa
    @6
    @0
    @8
    vx
    cA
    wph
    wps
    wch
    df-3an
    sbcbii
    @7
    wch
    vx
    cA
    sbcan
    @9
    @4
    @5
    wph
    wps
    vx
    cA
    sbcan
    anbi1i
    3bitri
    @2
    @3
    @5
    df-3an
    bitr4i
end
