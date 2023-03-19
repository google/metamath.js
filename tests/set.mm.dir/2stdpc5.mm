include "wi.mm"
include "wal.mm"
include "stdpc5.mm"
include "alimi.mm"
include "syl.mm"

theorem 2stdpc5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume 2stdpc5.1: |- F/ x ph
  assume 2stdpc5.2: |- F/ y ph


  assert |- ( A. x A. y ( ph -> ps ) -> ( ph -> A. x A. y ps ) )

  proof
    wph
    wps
    wi
    vy
    wal
    #
    vx
    wal
    wph
    wps
    vy
    wal
    #
    wi
    #
    vx
    wal
    wph
    @1
    vx
    wal
    wi
    @0
    @2
    vx
    wph
    wps
    vy
    2stdpc5.2
    stdpc5
    alimi
    wph
    @1
    vx
    2stdpc5.1
    stdpc5
    syl
end
