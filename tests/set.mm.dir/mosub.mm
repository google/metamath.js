include "cv.mm"
include "wceq.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "moeq.mm"
include "ax-gen.mm"
include "moexexv.mm"
include "mp2an.mm"

theorem mosub
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume mosub.1: |- E* x ph

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- E* x E. y ( y = A /\ ph )

  proof
    vy
    cv
    cA
    wceq
    #
    vy
    wmo
    wph
    vx
    wmo
    #
    vy
    wal
    @0
    wph
    wa
    vy
    wex
    vx
    wmo
    vy
    cA
    moeq
    @1
    vy
    mosub.1
    ax-gen
    @0
    wph
    vy
    vx
    moexexv
    mp2an
end
