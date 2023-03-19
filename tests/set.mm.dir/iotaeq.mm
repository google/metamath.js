include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "cab.mm"
include "csn.mm"
include "cuni.mm"
include "cio.mm"
include "wsb.mm"
include "wcel.mm"
include "drsb1.mm"
include "df-clab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eqeq1d.mm"
include "abbidv.mm"
include "unieqd.mm"
include "df-iota.mm"
include "3eqtr4g.mm"

theorem iotaeq
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> ( iota x ph ) = ( iota y ph ) )

  proof
    vx
    cv
    vy
    cv
    wceq
    vx
    wal
    #
    wph
    vx
    cab
    #
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    cab
    #
    cuni
    wph
    vy
    cab
    #
    @3
    wceq
    #
    vz
    cab
    #
    cuni
    wph
    vx
    cio
    wph
    vy
    cio
    @0
    @5
    @8
    @0
    @4
    @7
    vz
    @0
    @1
    @6
    @3
    @0
    vz
    @1
    @6
    @0
    wph
    vx
    vz
    wsb
    wph
    vy
    vz
    wsb
    @2
    @1
    wcel
    @2
    @6
    wcel
    wph
    vx
    vy
    vz
    drsb1
    wph
    vz
    vx
    df-clab
    wph
    vz
    vy
    df-clab
    3bitr4g
    eqrdv
    eqeq1d
    abbidv
    unieqd
    wph
    vx
    vz
    df-iota
    wph
    vy
    vz
    df-iota
    3eqtr4g
end
