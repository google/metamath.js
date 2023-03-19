include "com.mm"
include "cv.mm"
include "cvv.mm"
include "cuni.mm"
include "cun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "ciun.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wex.mm"
include "eqid.mm"
include "trcl.mm"
include "omex.mm"
include "fvex.mm"
include "iunex.mm"
include "wceq.mm"
include "sseq2.mm"
include "treq.mm"
include "sseq1.mm"
include "imbi2d.mm"
include "albidv.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "ax-mp.mm"

theorem tz9.1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  assume tz9.1.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint A w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- E. x ( A C_ x /\ Tr x /\ A. y ( ( A C_ y /\ Tr y ) -> x C_ y ) )

  proof
    cA
    vz
    com
    vz
    cv
    #
    vw
    cvv
    vw
    cv
    #
    @1
    cuni
    cun
    cmpt
    cA
    crdg
    com
    cres
    #
    cfv
    #
    ciun
    #
    wss
    #
    @4
    wtr
    #
    cA
    vy
    cv
    #
    wss
    @7
    wtr
    wa
    #
    @4
    @7
    wss
    #
    wi
    #
    vy
    wal
    #
    w3a
    #
    cA
    vx
    cv
    #
    wss
    #
    @13
    wtr
    #
    @8
    @13
    @7
    wss
    #
    wi
    #
    vy
    wal
    #
    w3a
    #
    vx
    wex
    vy
    vz
    vw
    cA
    @4
    @2
    tz9.1.1
    @2
    eqid
    @4
    eqid
    trcl
    @19
    @12
    vx
    @4
    vz
    com
    @3
    omex
    @0
    @2
    fvex
    iunex
    @13
    @4
    wceq
    #
    @14
    @5
    @15
    @6
    @18
    @11
    @13
    @4
    cA
    sseq2
    @13
    @4
    treq
    @20
    @17
    @10
    vy
    @20
    @16
    @9
    @8
    @13
    @4
    @7
    sseq1
    imbi2d
    albidv
    3anbi123d
    spcev
    ax-mp
end
