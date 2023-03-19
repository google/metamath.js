include "wi.mm"
include "wal.mm"
include "weq.mm"
include "wssb.mm"
include "imim2.mm"
include "al2imi.mm"
include "imim2d.mm"
include "alimdv.mm"
include "df-ssb.mm"
include "3imtr4g.mm"

theorem bj-ssbim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( A. x ( ph -> ps ) -> ( [b t /b x ]b ph -> [b t /b x ]b ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    #
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    vy
    wal
    @2
    @3
    wps
    wi
    #
    vx
    wal
    #
    wi
    #
    vy
    wal
    wph
    vx
    vt
    wssb
    wps
    vx
    vt
    wssb
    @1
    @6
    @9
    vy
    @1
    @5
    @8
    @2
    @0
    @4
    @7
    vx
    wph
    wps
    @3
    imim2
    al2imi
    imim2d
    alimdv
    wph
    vx
    vy
    vt
    df-ssb
    wps
    vx
    vy
    vt
    df-ssb
    3imtr4g
end
