include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "ccom.mm"
include "weq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "biimprd.mm"
include "spimev.mm"
include "ex.mm"
include "adantr.mm"
include "com12.mm"
include "a2i.mm"
include "19.37v.mm"
include "sylibr.mm"
include "2alimi.mm"
include "reflexg.mm"
include "cnvssco.mm"
include "3imtr4i.mm"

theorem refimssco
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( _I |` ( dom A u. ran A ) ) C_ A -> `' A C_ `' ( A o. A ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @0
    @0
    cA
    wbr
    #
    @1
    @1
    cA
    wbr
    #
    wa
    #
    wi
    #
    vy
    wal
    vx
    wal
    @2
    @0
    vz
    cv
    #
    cA
    wbr
    #
    @7
    @1
    cA
    wbr
    #
    wa
    #
    wi
    vz
    wex
    #
    vy
    wal
    vx
    wal
    cid
    cA
    cdm
    cA
    crn
    cun
    cres
    cA
    wss
    cA
    ccnv
    cA
    cA
    ccom
    ccnv
    wss
    @6
    @11
    vx
    vy
    @6
    @2
    @10
    vz
    wex
    #
    wi
    #
    @11
    @2
    @5
    @12
    @5
    @2
    @12
    @3
    @13
    @4
    @3
    @2
    @12
    @3
    @2
    wa
    #
    @10
    vz
    vx
    vz
    vx
    weq
    #
    @10
    @14
    @15
    @8
    @3
    @9
    @2
    @7
    @0
    @0
    cA
    breq2
    @7
    @0
    @1
    cA
    breq1
    anbi12d
    biimprd
    spimev
    ex
    adantr
    com12
    a2i
    @2
    @10
    vz
    19.37v
    sylibr
    2alimi
    vx
    vy
    cA
    reflexg
    vx
    vy
    vz
    cA
    cA
    cA
    cnvssco
    3imtr4i
end
