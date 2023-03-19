include "weq.mm"
include "wal.mm"
include "wnf.mm"
include "wn.mm"
include "wa.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfald.mm"
include "ex.mm"
include "nfa1.mm"
include "biidd.mm"
include "drnf1.mm"
include "mpbiri.mm"
include "pm2.61d2.mm"

theorem nfald2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfald2.1: |- F/ y ph
  assume nfald2.2: |- ( ( ph /\ -. A. x x = y ) -> F/ x ps )


  assert |- ( ph -> F/ x A. y ps )

  proof
    wph
    vx
    vy
    weq
    vx
    wal
    #
    wps
    vy
    wal
    #
    vx
    wnf
    #
    wph
    @0
    wn
    #
    @2
    wph
    @3
    wa
    wps
    vx
    vy
    wph
    @3
    vy
    nfald2.1
    vx
    vy
    vy
    nfnae
    nfan
    nfald2.2
    nfald
    ex
    @0
    @2
    @1
    vy
    wnf
    wps
    vy
    nfa1
    @1
    @1
    vx
    vy
    @0
    @1
    biidd
    drnf1
    mpbiri
    pm2.61d2
end
