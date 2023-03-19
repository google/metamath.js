include "coprab.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wb.mm"
include "ssoprab2b.mm"
include "anbi12i.mm"
include "eqss.mm"
include "2albiim.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"
include "3bitr4i.mm"

theorem eqoprab2b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph <-> ps ) )

  proof
    wph
    vx
    vy
    vz
    coprab
    #
    wps
    vx
    vy
    vz
    coprab
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
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    wps
    wph
    wi
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    wa
    #
    @0
    @1
    wceq
    wph
    wps
    wb
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    @2
    @5
    @3
    @7
    wph
    wps
    vx
    vy
    vz
    ssoprab2b
    wps
    wph
    vx
    vy
    vz
    ssoprab2b
    anbi12i
    @0
    @1
    eqss
    @10
    @4
    @6
    wa
    #
    vx
    wal
    @8
    @9
    @11
    vx
    wph
    wps
    vy
    vz
    2albiim
    albii
    @4
    @6
    vx
    19.26
    bitri
    3bitr4i
end
