include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wb.mm"
include "nfa1.mm"
include "drsb2.mm"
include "sbbid.mm"
include "wn.mm"
include "wi.mm"
include "sb4b.mm"
include "sbequ.mm"
include "pm5.74i.mm"
include "albii.mm"
include "syl6bb.mm"
include "bitr4d.mm"
include "pm2.61i.mm"

theorem sbcom3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( [ z / y ] [ y / x ] ph <-> [ z / y ] [ z / x ] ph )

  proof
    vy
    vz
    weq
    #
    vy
    wal
    #
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    wsb
    #
    wph
    vx
    vz
    wsb
    #
    vy
    vz
    wsb
    #
    wb
    @1
    @2
    @4
    vy
    vz
    @0
    vy
    nfa1
    wph
    vy
    vz
    vx
    drsb2
    sbbid
    @1
    wn
    #
    @3
    @0
    @4
    wi
    #
    vy
    wal
    #
    @5
    @6
    @3
    @0
    @2
    wi
    #
    vy
    wal
    @8
    @2
    vy
    vz
    sb4b
    @9
    @7
    vy
    @0
    @2
    @4
    wph
    vy
    vz
    vx
    sbequ
    pm5.74i
    albii
    syl6bb
    @4
    vy
    vz
    sb4b
    bitr4d
    pm2.61i
end
