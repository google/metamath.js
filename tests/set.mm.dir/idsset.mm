include "cid.mm"
include "csset.mm"
include "ccnv.mm"
include "cin.mm"
include "reli.mm"
include "wrel.mm"
include "relsset.mm"
include "relin1.mm"
include "ax-mp.mm"
include "weq.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wbr.mm"
include "eqss.mm"
include "vex.mm"
include "ideq.mm"
include "brin.mm"
include "brsset.mm"
include "brcnv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "eqbrriv.mm"

theorem idsset
  let vy: setvar y
  let vz: setvar z


  assert |- _I = ( SSet i^i `' SSet )

  proof
    vy
    vz
    cid
    csset
    csset
    ccnv
    #
    cin
    #
    reli
    csset
    wrel
    @1
    wrel
    relsset
    csset
    @0
    relin1
    ax-mp
    vy
    vz
    weq
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    #
    @2
    @3
    cid
    wbr
    @2
    @3
    @1
    wbr
    #
    @2
    @3
    eqss
    @2
    @3
    vz
    vex
    #
    ideq
    @7
    @2
    @3
    csset
    wbr
    #
    @2
    @3
    @0
    wbr
    #
    wa
    @6
    @2
    @3
    csset
    @0
    brin
    @9
    @4
    @10
    @5
    @2
    @3
    @8
    brsset
    @10
    @3
    @2
    csset
    wbr
    @5
    @2
    @3
    csset
    vy
    vex
    #
    @8
    brcnv
    @3
    @2
    @11
    brsset
    bitri
    anbi12i
    bitri
    3bitr4i
    eqbrriv
end
