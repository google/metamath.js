include "wcel.mm"
include "w3o.mm"
include "wsbc.mm"
include "wo.mm"
include "wb.mm"
include "sbcor.mm"
include "a1i.mm"
include "df-3or.mm"
include "bicomi.mm"
include "sbcbii.mm"
include "orbi1d.mm"
include "3bitr3d.mm"
include "syl6bbr.mm"

theorem sbc3orgOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( [. A / x ]. ( ph \/ ps \/ ch ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps \/ [. A / x ]. ch ) ) )

  proof
    cA
    cV
    wcel
    #
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
    @3
    @4
    @6
    w3o
    @0
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
    #
    @8
    vx
    cA
    wsbc
    #
    @6
    wo
    #
    @2
    @7
    @10
    @12
    wb
    @0
    @8
    wch
    vx
    cA
    sbcor
    a1i
    @10
    @2
    wb
    @0
    @9
    @1
    vx
    cA
    @1
    @9
    wph
    wps
    wch
    df-3or
    bicomi
    sbcbii
    a1i
    @0
    @11
    @5
    @6
    @11
    @5
    wb
    @0
    wph
    wps
    vx
    cA
    sbcor
    a1i
    orbi1d
    3bitr3d
    @3
    @4
    @6
    df-3or
    syl6bbr
end
