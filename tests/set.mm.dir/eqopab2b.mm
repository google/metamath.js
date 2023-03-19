include "copab.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wb.mm"
include "ssopab2b.mm"
include "anbi12i.mm"
include "eqss.mm"
include "2albiim.mm"
include "3bitr4i.mm"

theorem eqopab2b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( { <. x , y >. | ph } = { <. x , y >. | ps } <-> A. x A. y ( ph <-> ps ) )

  proof
    wph
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    #
    wss
    #
    @1
    @0
    wss
    #
    wa
    wph
    wps
    wi
    vy
    wal
    vx
    wal
    #
    wps
    wph
    wi
    vy
    wal
    vx
    wal
    #
    wa
    @0
    @1
    wceq
    wph
    wps
    wb
    vy
    wal
    vx
    wal
    @2
    @4
    @3
    @5
    wph
    wps
    vx
    vy
    ssopab2b
    wps
    wph
    vx
    vy
    ssopab2b
    anbi12i
    @0
    @1
    eqss
    wph
    wps
    vx
    vy
    2albiim
    3bitr4i
end
