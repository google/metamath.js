include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wmo.mm"
include "csb.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "eqtr2.mm"
include "vex.mm"
include "opth.mm"
include "simprbi.mm"
include "syl.mm"
include "gen2.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfop.mm"
include "nfeq2.mm"
include "csbeq1a.mm"
include "id.mm"
include "opeq12d.mm"
include "eqeq2d.mm"
include "mo4f.mm"
include "mpbir.mm"

theorem moop2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume moop2.1: |- B e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- E* x A = <. B , x >.

  proof
    cA
    cB
    vx
    cv
    #
    cop
    #
    wceq
    #
    vx
    wmo
    @2
    cA
    vx
    vy
    cv
    #
    cB
    csb
    #
    @3
    cop
    #
    wceq
    #
    wa
    #
    @0
    @3
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @9
    vx
    vy
    @7
    @1
    @5
    wceq
    #
    @8
    cA
    @1
    @5
    eqtr2
    @10
    cB
    @4
    wceq
    @8
    cB
    @0
    @4
    @3
    moop2.1
    vx
    vex
    opth
    simprbi
    syl
    gen2
    @2
    @6
    vx
    vy
    vx
    cA
    @5
    vx
    @4
    @3
    vx
    @3
    cB
    nfcsb1v
    vx
    @3
    nfcv
    nfop
    nfeq2
    @8
    @1
    @5
    cA
    @8
    cB
    @4
    @0
    @3
    vx
    @3
    cB
    csbeq1a
    @8
    id
    opeq12d
    eqeq2d
    mo4f
    mpbir
end
