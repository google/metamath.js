include "w3a.mm"
include "wsb.mm"
include "wa.mm"
include "df-3an.mm"
include "sbbii.mm"
include "sban.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem sb3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ( ph /\ ps /\ ch ) <-> ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) )

  proof
    wph
    wps
    wch
    w3a
    #
    vx
    vy
    wsb
    wph
    wps
    wa
    #
    wch
    wa
    #
    vx
    vy
    wsb
    @1
    vx
    vy
    wsb
    #
    wch
    vx
    vy
    wsb
    #
    wa
    #
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    @4
    w3a
    #
    @0
    @2
    vx
    vy
    wph
    wps
    wch
    df-3an
    sbbii
    @1
    wch
    vx
    vy
    sban
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
    vy
    sban
    anbi1i
    @6
    @7
    @4
    df-3an
    bitr4i
    3bitri
end
