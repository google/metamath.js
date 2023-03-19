include "weq.mm"
include "wal.mm"
include "hbae-o.mm"
include "biimpd.mm"
include "alimdh.mm"
include "ax-c11.mm"
include "syld.mm"
include "biimprd.mm"
include "wi.mm"
include "aecoms-o.mm"
include "impbid.mm"

theorem dral1-o
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume dral1-o.1: |- ( A. x x = y -> ( ph <-> ps ) )


  assert |- ( A. x x = y -> ( A. x ph <-> A. y ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    vy
    wal
    #
    @0
    @1
    wps
    vx
    wal
    @2
    @0
    wph
    wps
    vx
    vx
    vy
    vx
    hbae-o
    @0
    wph
    wps
    dral1-o.1
    biimpd
    alimdh
    wps
    vx
    vy
    ax-c11
    syld
    @0
    @2
    wph
    vy
    wal
    #
    @1
    @0
    wps
    wph
    vy
    vx
    vy
    vy
    hbae-o
    @0
    wph
    wps
    dral1-o.1
    biimprd
    alimdh
    @3
    @1
    wi
    vy
    vx
    wph
    vy
    vx
    ax-c11
    aecoms-o
    syld
    impbid
end
