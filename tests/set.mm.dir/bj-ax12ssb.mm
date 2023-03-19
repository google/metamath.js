include "wssb.mm"
include "wi.mm"
include "weq.mm"
include "wal.mm"
include "bj-ax12.mm"
include "bj-ssb1.mm"
include "imbi2i.mm"
include "albii.mm"
include "mpbir.mm"

theorem bj-ax12ssb
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t

  disjoint t x
  assert |- [b t /b x ]b ( ph -> [b t /b x ]b ph )

  proof
    wph
    wph
    vx
    vt
    wssb
    #
    wi
    #
    vx
    vt
    wssb
    vx
    vt
    weq
    #
    @1
    wi
    #
    vx
    wal
    #
    @4
    @2
    wph
    @2
    wph
    wi
    vx
    wal
    #
    wi
    #
    wi
    #
    vx
    wal
    wph
    vx
    vt
    bj-ax12
    @3
    @7
    vx
    @1
    @6
    @2
    @0
    @5
    wph
    wph
    vx
    vt
    bj-ssb1
    imbi2i
    imbi2i
    albii
    mpbir
    @1
    vx
    vt
    bj-ssb1
    mpbir
end
