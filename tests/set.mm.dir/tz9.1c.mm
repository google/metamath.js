include "cv.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "com.mm"
include "cuni.mm"
include "cun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "ciun.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "eqid.mm"
include "trcl.mm"
include "3simpa.mm"
include "omex.mm"
include "fvex.mm"
include "iunex.mm"
include "wceq.mm"
include "sseq2.mm"
include "treq.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mp2b.mm"
include "abn0.mm"
include "mpbir.mm"
include "intex.mm"
include "mpbi.mm"

theorem tz9.1c
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume tz9.1.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- |^| { x | ( A C_ x /\ Tr x ) } e. _V

  proof
    cA
    vx
    cv
    #
    wss
    #
    @0
    wtr
    #
    wa
    #
    vx
    cab
    #
    c0
    wne
    #
    @4
    cint
    cvv
    wcel
    @5
    @3
    vx
    wex
    #
    cA
    vw
    com
    vw
    cv
    #
    vz
    cvv
    vz
    cv
    #
    @8
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
    @11
    wtr
    #
    @3
    @11
    @0
    wss
    wi
    vx
    wal
    #
    w3a
    @12
    @13
    wa
    #
    @6
    vx
    vw
    vz
    cA
    @11
    @9
    tz9.1.1
    @9
    eqid
    @11
    eqid
    trcl
    @12
    @13
    @14
    3simpa
    @3
    @15
    vx
    @11
    vw
    com
    @10
    omex
    @7
    @9
    fvex
    iunex
    @0
    @11
    wceq
    @1
    @12
    @2
    @13
    @0
    @11
    cA
    sseq2
    @0
    @11
    treq
    anbi12d
    spcev
    mp2b
    @3
    vx
    abn0
    mpbir
    @4
    intex
    mpbi
end
