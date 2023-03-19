include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "cc.mm"
include "wcel.mm"
include "climcl.mm"
include "breq2.mm"
include "spcegv.mm"
include "mpcom.mm"
include "climuni.mm"
include "gen2.mm"
include "jctir.mm"
include "nfv.mm"
include "cbveu.mm"
include "eu4.mm"
include "bitri.mm"
include "sylibr.mm"

theorem climeu
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint F x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- ( F ~~> A -> E! x F ~~> x )

  proof
    cF
    cA
    cli
    wbr
    #
    cF
    vy
    cv
    #
    cli
    wbr
    #
    vy
    wex
    #
    @2
    cF
    vx
    cv
    #
    cli
    wbr
    #
    wa
    vy
    vx
    weq
    wi
    #
    vx
    wal
    vy
    wal
    #
    wa
    #
    @5
    vx
    weu
    #
    @0
    @3
    @7
    cA
    cc
    wcel
    @0
    @3
    cA
    cF
    climcl
    @2
    @0
    vy
    cA
    cc
    @1
    cA
    cF
    cli
    breq2
    spcegv
    mpcom
    @6
    vy
    vx
    @1
    @4
    cF
    climuni
    gen2
    jctir
    @9
    @2
    vy
    weu
    @8
    @5
    @2
    vx
    vy
    @5
    vy
    nfv
    @2
    vx
    nfv
    @4
    @1
    cF
    cli
    breq2
    cbveu
    @2
    @5
    vy
    vx
    @1
    @4
    cF
    cli
    breq2
    eu4
    bitri
    sylibr
end
