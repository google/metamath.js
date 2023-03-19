include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "weu.mm"
include "wral.mm"
include "wb.mm"
include "wal.mm"
include "cio.mm"
include "nfeu1.mm"
include "eusvobj2.mm"
include "alrimi.mm"
include "iotabi.mm"
include "syl.mm"

theorem eusvobj1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume eusvobj1.1: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( E! x E. y e. A x = B -> ( iota x E. y e. A x = B ) = ( iota x A. y e. A x = B ) )

  proof
    vx
    cv
    cB
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    weu
    #
    @1
    @0
    vy
    cA
    wral
    #
    wb
    #
    vx
    wal
    @1
    vx
    cio
    @3
    vx
    cio
    wceq
    @2
    @4
    vx
    @1
    vx
    nfeu1
    vx
    vy
    cA
    cB
    eusvobj1.1
    eusvobj2
    alrimi
    @1
    @3
    vx
    iotabi
    syl
end
