include "wn.mm"
include "wal.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "ax-5.mm"
include "wsb.mm"
include "bj-stdpc4v.mm"
include "sbn.mm"
include "sylib.mm"
include "df-clab.mm"
include "sylnibr.mm"
include "alrimih.mm"
include "eq0.mm"
include "sylibr.mm"

theorem bj-ab0
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x -. ph -> { x | ph } = (/) )

  proof
    wph
    wn
    #
    vx
    wal
    #
    vy
    cv
    wph
    vx
    cab
    #
    wcel
    #
    wn
    #
    vy
    wal
    @2
    c0
    wceq
    @1
    @4
    vy
    @1
    vy
    ax-5
    @1
    wph
    vx
    vy
    wsb
    #
    @3
    @1
    @0
    vx
    vy
    wsb
    @5
    wn
    @0
    vx
    vy
    bj-stdpc4v
    wph
    vx
    vy
    sbn
    sylib
    wph
    vy
    vx
    df-clab
    sylnibr
    alrimih
    vy
    @2
    eq0
    sylibr
end
