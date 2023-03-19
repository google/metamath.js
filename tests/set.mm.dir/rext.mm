include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "csn.mm"
include "wceq.mm"
include "vsnid.mm"
include "snex.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "spcv.mm"
include "mpi.mm"
include "velsn.mm"
include "equcomi.mm"
include "sylbi.mm"
include "syl.mm"

theorem rext
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A. z ( x e. z -> y e. z ) -> x = y )

  proof
    vx
    cv
    #
    vz
    cv
    #
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wi
    #
    vz
    wal
    #
    @3
    @0
    csn
    #
    wcel
    #
    @0
    @3
    wceq
    #
    @6
    @0
    @7
    wcel
    #
    @8
    vx
    vsnid
    @5
    @10
    @8
    wi
    vz
    @7
    @0
    snex
    @1
    @7
    wceq
    @2
    @10
    @4
    @8
    @1
    @7
    @0
    eleq2
    @1
    @7
    @3
    eleq2
    imbi12d
    spcv
    mpi
    @8
    @3
    @0
    wceq
    @9
    vy
    @0
    velsn
    vy
    vx
    equcomi
    sylbi
    syl
end
