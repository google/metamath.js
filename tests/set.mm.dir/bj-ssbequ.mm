include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "equequ2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "df-ssb.mm"
include "3bitr4g.mm"

theorem bj-ssbequ
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vs: setvar s
  let vy: setvar y


  assert |- ( s = t -> ( [b s /b x ]b ph <-> [b t /b x ]b ph ) )

  proof
    vs
    vt
    weq
    #
    vy
    vs
    weq
    #
    vx
    vy
    weq
    wph
    wi
    vx
    wal
    #
    wi
    #
    vy
    wal
    vy
    vt
    weq
    #
    @2
    wi
    #
    vy
    wal
    wph
    vx
    vs
    wssb
    wph
    vx
    vt
    wssb
    @0
    @3
    @5
    vy
    @0
    @1
    @4
    @2
    vs
    vt
    vy
    equequ2
    imbi1d
    albidv
    wph
    vx
    vy
    vs
    df-ssb
    wph
    vx
    vy
    vt
    df-ssb
    3bitr4g
end
