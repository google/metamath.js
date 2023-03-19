include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "bj-ssb1.mm"
include "bj-ssbbii.mm"
include "df-ssb.mm"
include "3bitr4i.mm"

theorem bj-ssbssblem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t

  disjoint t y
  disjoint x y
  disjoint ph y
  assert |- ( [b t /b y ]b [b y /b x ]b ph <-> [b t /b x ]b ph )

  proof
    vx
    vy
    weq
    wph
    wi
    vx
    wal
    #
    vy
    vt
    wssb
    vy
    vt
    weq
    @0
    wi
    vy
    wal
    wph
    vx
    vy
    wssb
    #
    vy
    vt
    wssb
    wph
    vx
    vt
    wssb
    @0
    vy
    vt
    bj-ssb1
    @1
    @0
    vy
    vt
    wph
    vx
    vy
    bj-ssb1
    bj-ssbbii
    wph
    vx
    vy
    vt
    df-ssb
    3bitr4i
end
