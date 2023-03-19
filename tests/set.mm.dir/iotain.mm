include "weu.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cio.mm"
include "df-eu.mm"
include "csn.mm"
include "vex.mm"
include "intsn.mm"
include "nfa1.mm"
include "sp.mm"
include "abbid.mm"
include "df-sn.mm"
include "syl6eqr.mm"
include "inteqd.mm"
include "iotaval.mm"
include "3eqtr4a.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem iotain
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x ph -> |^| { x | ph } = ( iota x ph ) )

  proof
    wph
    vx
    weu
    wph
    vx
    cv
    vy
    cv
    #
    wceq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    cab
    #
    cint
    #
    wph
    vx
    cio
    #
    wceq
    #
    wph
    vx
    vy
    df-eu
    @3
    @7
    vy
    @3
    @0
    csn
    #
    cint
    @0
    @5
    @6
    @0
    vy
    vex
    intsn
    @3
    @4
    @8
    @3
    @4
    @1
    vx
    cab
    @8
    @3
    wph
    @1
    vx
    @2
    vx
    nfa1
    @2
    vx
    sp
    abbid
    vx
    @0
    df-sn
    syl6eqr
    inteqd
    wph
    vx
    vy
    iotaval
    3eqtr4a
    exlimiv
    sylbi
end
