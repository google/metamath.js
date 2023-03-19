include "wnf.mm"
include "wal.mm"
include "weq.mm"
include "wi.mm"
include "wex.mm"
include "19.9t.mm"
include "biimpd.mm"
include "alimi.mm"
include "nf5r.mm"
include "bj-cbv3ta.mm"
include "syl2ani.mm"

theorem bj-cbv3tb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( x = y -> ( ph -> ps ) ) -> ( ( A. y F/ x ps /\ A. x F/ y ph ) -> ( A. x ph -> A. y ps ) ) )

  proof
    wps
    vx
    wnf
    #
    vy
    wal
    vx
    vy
    weq
    wph
    wps
    wi
    wi
    vy
    wal
    vx
    wal
    wps
    vx
    wex
    #
    wps
    wi
    #
    vy
    wal
    wph
    wph
    vy
    wal
    wi
    #
    vx
    wal
    wph
    vx
    wal
    wps
    vy
    wal
    wi
    wph
    vy
    wnf
    #
    vx
    wal
    @0
    @2
    vy
    @0
    @1
    wps
    wps
    vx
    19.9t
    biimpd
    alimi
    @4
    @3
    vx
    wph
    vy
    nf5r
    alimi
    wph
    wps
    vx
    vy
    bj-cbv3ta
    syl2ani
end
