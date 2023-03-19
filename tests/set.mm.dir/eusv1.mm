include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "weu.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "sp.mm"
include "eqtr3.mm"
include "syl2an.mm"
include "gen2.mm"
include "eqeq1.mm"
include "albidv.mm"
include "eu4.mm"
include "mpbiran2.mm"

theorem eusv1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( E! y A. x y = A <-> E. y A. x y = A )

  proof
    vy
    cv
    #
    cA
    wceq
    #
    vx
    wal
    #
    vy
    weu
    @2
    vy
    wex
    @2
    vz
    cv
    #
    cA
    wceq
    #
    vx
    wal
    #
    wa
    @0
    @3
    wceq
    #
    wi
    #
    vz
    wal
    vy
    wal
    @7
    vy
    vz
    @2
    @1
    @4
    @6
    @5
    @1
    vx
    sp
    @4
    vx
    sp
    @0
    @3
    cA
    eqtr3
    syl2an
    gen2
    @2
    @5
    vy
    vz
    @6
    @1
    @4
    vx
    @0
    @3
    cA
    eqeq1
    albidv
    eu4
    mpbiran2
end
