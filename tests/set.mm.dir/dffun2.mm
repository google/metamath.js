include "wfun.mm"
include "wrel.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "df-fun.mm"
include "wex.mm"
include "copab.mm"
include "df-id.mm"
include "sseq2i.mm"
include "df-co.mm"
include "sseq1i.mm"
include "ssopab2b.mm"
include "3bitri.mm"
include "vex.mm"
include "brcnv.mm"
include "anbi1i.mm"
include "exbii.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "alcom.mm"
include "bitri.mm"
include "anbi2i.mm"

theorem dffun2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( Fun A <-> ( Rel A /\ A. x A. y A. z ( ( x A y /\ x A z ) -> y = z ) ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    cA
    cA
    ccnv
    #
    ccom
    #
    cid
    wss
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @4
    vz
    cv
    cA
    wbr
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    wa
    cA
    df-fun
    @3
    @12
    @0
    @3
    @5
    @4
    @1
    wbr
    #
    @7
    wa
    #
    vx
    wex
    #
    @9
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    @11
    vx
    wal
    #
    vy
    wal
    @12
    @3
    @2
    @9
    vy
    vz
    copab
    #
    wss
    @15
    vy
    vz
    copab
    #
    @20
    wss
    @18
    cid
    @20
    @2
    vy
    vz
    df-id
    sseq2i
    @2
    @21
    @20
    vy
    vz
    vx
    cA
    @1
    df-co
    sseq1i
    @15
    @9
    vy
    vz
    ssopab2b
    3bitri
    @17
    @19
    vy
    @17
    @10
    vx
    wal
    #
    vz
    wal
    @19
    @16
    @22
    vz
    @16
    @8
    vx
    wex
    #
    @9
    wi
    @22
    @15
    @23
    @9
    @14
    @8
    vx
    @13
    @6
    @7
    @5
    @4
    cA
    vy
    vex
    vx
    vex
    brcnv
    anbi1i
    exbii
    imbi1i
    @8
    @9
    vx
    19.23v
    bitr4i
    albii
    @10
    vz
    vx
    alcom
    bitri
    albii
    @11
    vy
    vx
    alcom
    3bitri
    anbi2i
    bitri
end
