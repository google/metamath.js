include "wex.mm"
include "wb.mm"
include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "nfe1.mm"
include "19.9.mm"
include "biidd.mm"
include "drex1.mm"
include "drex2.mm"
include "excom.mm"
include "syl6bb.mm"
include "syl5rbbr.mm"
include "aecoms.mm"

theorem e2ebind
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> ( E. x E. y ph <-> E. y ph ) )

  proof
    wph
    vy
    wex
    #
    vx
    wex
    #
    @0
    wb
    vy
    vx
    @0
    @0
    vy
    wex
    #
    vy
    cv
    vx
    cv
    wceq
    vy
    wal
    #
    @1
    @0
    vy
    wph
    vy
    nfe1
    19.9
    @3
    @2
    wph
    vx
    wex
    #
    vy
    wex
    @1
    @0
    @4
    vy
    vx
    vy
    wph
    wph
    vy
    vx
    @3
    wph
    biidd
    drex1
    drex2
    wph
    vy
    vx
    excom
    syl6bb
    syl5rbbr
    aecoms
end
