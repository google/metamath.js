include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "weu.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cmpt.mm"
include "mptex.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "eqid.mm"
include "fnmpti.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "pm4.71ri.mm"
include "dffn5.mm"
include "eqeq1.mm"
include "sylbi.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "bitr2i.mm"
include "mpg.mm"
include "df-eu.mm"
include "mpbir.mm"

theorem eufnfv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vz: setvar z
  assume eufnfv.1: |- A e. _V
  assume eufnfv.2: |- B e. _V

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint B f
  disjoint f z
  disjoint x z
  disjoint A z
  disjoint B z
  assert |- E! f ( f Fn A /\ A. x e. A ( f ` x ) = B )

  proof
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    #
    cB
    wceq
    vx
    cA
    wral
    #
    wa
    #
    vf
    weu
    @5
    @0
    vz
    cv
    #
    wceq
    #
    wb
    #
    vf
    wal
    #
    vz
    wex
    #
    @5
    @0
    vx
    cA
    cB
    cmpt
    #
    wceq
    #
    wb
    #
    @10
    vf
    @9
    @13
    vf
    wal
    vz
    @11
    vx
    cA
    cB
    eufnfv.1
    mptex
    @6
    @11
    wceq
    #
    @8
    @13
    vf
    @14
    @7
    @12
    @5
    @6
    @11
    @0
    eqeq2
    bibi2d
    albidv
    spcev
    @12
    @1
    @12
    wa
    @5
    @12
    @1
    @12
    @1
    @11
    cA
    wfn
    vx
    cA
    cB
    @11
    eufnfv.2
    @11
    eqid
    fnmpti
    cA
    @0
    @11
    fneq1
    mpbiri
    pm4.71ri
    @1
    @12
    @4
    @1
    @12
    vx
    cA
    @3
    cmpt
    #
    @11
    wceq
    #
    @4
    @1
    @0
    @15
    wceq
    @12
    @16
    wb
    vx
    cA
    @0
    dffn5
    @0
    @15
    @11
    eqeq1
    sylbi
    @3
    cvv
    wcel
    #
    vx
    cA
    wral
    @16
    @4
    wb
    @17
    vx
    cA
    @2
    @0
    fvex
    rgenw
    vx
    cA
    @3
    cB
    cvv
    mpteqb
    ax-mp
    syl6bb
    pm5.32i
    bitr2i
    mpg
    @5
    vf
    vz
    df-eu
    mpbir
end
