include "weq.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "wa.mm"
include "bj-spimt2.mm"
include "imp.mm"
include "alanimi.mm"
include "bj-hbalt.mm"
include "sylgt.mm"
include "syl2im.mm"
include "expimpd.mm"
include "alcoms.mm"

theorem bj-cbv3ta
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( x = y -> ( ph -> ps ) ) -> ( ( A. y ( E. x ps -> ps ) /\ A. x ( ph -> A. y ph ) ) -> ( A. x ph -> A. y ps ) ) )

  proof
    vx
    vy
    weq
    wph
    wps
    wi
    wi
    #
    wps
    vx
    wex
    wps
    wi
    #
    vy
    wal
    #
    wph
    wph
    vy
    wal
    wi
    vx
    wal
    #
    wa
    wph
    vx
    wal
    #
    wps
    vy
    wal
    wi
    #
    wi
    vy
    vx
    @0
    vx
    wal
    #
    vy
    wal
    #
    @2
    @3
    @5
    @7
    @2
    wa
    @4
    wps
    wi
    #
    vy
    wal
    @3
    @4
    @4
    vy
    wal
    wi
    @5
    @6
    @1
    @8
    vy
    @6
    @1
    @8
    wph
    wps
    vx
    vy
    bj-spimt2
    imp
    alanimi
    wph
    vy
    vx
    bj-hbalt
    @4
    @4
    wps
    vy
    sylgt
    syl2im
    expimpd
    alcoms
end
