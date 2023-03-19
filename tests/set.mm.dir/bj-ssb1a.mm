include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "wex.mm"
include "ax-1.mm"
include "19.23v.mm"
include "sylibr.mm"
include "equequ2.mm"
include "imbi1d.mm"
include "pm5.74i.mm"
include "albii.mm"
include "alimi.mm"
include "bj-ssblem2.mm"
include "stdpc5v.mm"
include "3syl.mm"
include "df-ssb.mm"

theorem bj-ssb1a
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y

  disjoint t x
  disjoint x y
  disjoint t y
  disjoint ph y
  assert |- ( A. x ( x = t -> ph ) -> [b t /b x ]b ph )

  proof
    vx
    vt
    weq
    #
    wph
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
    wi
    #
    vy
    wal
    #
    wph
    vx
    vt
    wssb
    @2
    @3
    @5
    wi
    #
    vy
    wal
    #
    vx
    wal
    @8
    vx
    wal
    #
    vy
    wal
    @7
    @1
    @9
    vx
    @1
    @3
    @1
    wi
    #
    vy
    wal
    #
    @9
    @1
    @3
    vy
    wex
    #
    @1
    wi
    @12
    @1
    @13
    ax-1
    @3
    @1
    vy
    19.23v
    sylibr
    @8
    @11
    vy
    @3
    @5
    @1
    @3
    @4
    @0
    wph
    vy
    vt
    vx
    equequ2
    imbi1d
    pm5.74i
    albii
    sylibr
    alimi
    wph
    vx
    vy
    vt
    bj-ssblem2
    @10
    @6
    vy
    @3
    @5
    vx
    stdpc5v
    alimi
    3syl
    wph
    vx
    vy
    vt
    df-ssb
    sylibr
end
