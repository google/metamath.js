include "wa.mm"
include "wex.mm"
include "nfe1.mm"
include "weq.mm"
include "wal.mm"
include "wi.mm"
include "19.8a.mm"
include "anim2i.mm"
include "eximi.mm"
include "biidd.mm"
include "drex1.mm"
include "syl5ibr.mm"
include "wn.mm"
include "19.40.mm"
include "19.9d.mm"
include "anim1d.mm"
include "syl56.mm"
include "pm2.61i.mm"
include "exlimi.mm"

theorem exdistrf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume exdistrf.1: |- ( -. A. x x = y -> F/ y ph )


  assert |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) )

  proof
    wph
    wps
    wa
    #
    vy
    wex
    #
    wph
    wps
    vy
    wex
    #
    wa
    #
    vx
    wex
    #
    vx
    @3
    vx
    nfe1
    vx
    vy
    weq
    vx
    wal
    #
    @1
    @4
    wi
    @1
    @4
    @5
    @3
    vy
    wex
    @0
    @3
    vy
    wps
    @2
    wph
    wps
    vy
    19.8a
    anim2i
    eximi
    @3
    @3
    vx
    vy
    @5
    @3
    biidd
    drex1
    syl5ibr
    @1
    wph
    vy
    wex
    #
    @2
    wa
    @5
    wn
    #
    @3
    @4
    wph
    wps
    vy
    19.40
    @7
    @6
    wph
    @2
    wph
    @7
    vy
    exdistrf.1
    19.9d
    anim1d
    @3
    vx
    19.8a
    syl56
    pm2.61i
    exlimi
end
