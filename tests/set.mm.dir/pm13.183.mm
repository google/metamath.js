include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "eqeq1.mm"
include "eqeq2.mm"
include "bibi1d.mm"
include "albidv.mm"
include "alrimiv.mm"
include "wsb.mm"
include "stdpc4.mm"
include "sbbi.mm"
include "eqsb3.mm"
include "bibi2i.mm"
include "equsb1.mm"
include "biimp.mm"
include "mpi.mm"
include "sylbi.mm"
include "syl.mm"
include "impbii.mm"
include "vtoclbg.mm"

theorem pm13.183
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A z
  disjoint B z
  disjoint A y
  disjoint y z
  disjoint B y
  assert |- ( A e. V -> ( A = B <-> A. z ( z = A <-> z = B ) ) )

  proof
    vy
    cv
    #
    cB
    wceq
    #
    vz
    cv
    #
    @0
    wceq
    #
    @2
    cB
    wceq
    #
    wb
    #
    vz
    wal
    #
    cA
    cB
    wceq
    @2
    cA
    wceq
    #
    @4
    wb
    #
    vz
    wal
    vy
    cA
    cV
    @0
    cA
    cB
    eqeq1
    @0
    cA
    wceq
    #
    @5
    @8
    vz
    @9
    @3
    @7
    @4
    @0
    cA
    @2
    eqeq2
    bibi1d
    albidv
    @1
    @6
    @1
    @5
    vz
    @0
    cB
    @2
    eqeq2
    alrimiv
    @6
    @5
    vz
    vy
    wsb
    #
    @1
    @5
    vz
    vy
    stdpc4
    @10
    @3
    vz
    vy
    wsb
    #
    @4
    vz
    vy
    wsb
    #
    wb
    #
    @1
    @3
    @4
    vz
    vy
    sbbi
    @13
    @11
    @1
    wb
    #
    @1
    @12
    @1
    @11
    vy
    vz
    cB
    eqsb3
    bibi2i
    @14
    @11
    @1
    vz
    vy
    equsb1
    @11
    @1
    biimp
    mpi
    sylbi
    sylbi
    syl
    impbii
    vtoclbg
end
