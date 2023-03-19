include "w3o.mm"
include "wsbc.mm"
include "wo.mm"
include "sbcor.mm"
include "df-3or.mm"
include "bicomi.mm"
include "sbcbii.mm"
include "orbi1i.mm"
include "3bitr3i.mm"
include "bitr4i.mm"

theorem sbc3or
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A


  assert |- ( [. A / x ]. ( ph \/ ps \/ ch ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps \/ [. A / x ]. ch ) )

  proof
    wph
    wps
    wch
    w3o
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
    wo
    #
    wch
    vx
    cA
    wsbc
    #
    wo
    #
    @2
    @3
    @5
    w3o
    wph
    wps
    wo
    #
    wch
    wo
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
    wo
    @1
    @6
    @7
    wch
    vx
    cA
    sbcor
    @8
    @0
    vx
    cA
    @0
    @8
    wph
    wps
    wch
    df-3or
    bicomi
    sbcbii
    @9
    @4
    @5
    wph
    wps
    vx
    cA
    sbcor
    orbi1i
    3bitr3i
    @2
    @3
    @5
    df-3or
    bitr4i
end
