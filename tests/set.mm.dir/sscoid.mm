include "cid.mm"
include "ccom.mm"
include "wss.mm"
include "wrel.mm"
include "relco.mm"
include "relss.mm"
include "mpi.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "elrel.mm"
include "wbr.mm"
include "vex.mm"
include "brco.mm"
include "weq.mm"
include "ancom.mm"
include "ideq.mm"
include "anbi1i.mm"
include "bitri.mm"
include "exbii.mm"
include "breq2.mm"
include "ceqsexv.mm"
include "a1i.mm"
include "eleq1.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "3bitr4d.mm"
include "exlimivv.mm"
include "syl.mm"
include "pm5.74da.mm"
include "albidv.mm"
include "dfss2.mm"
include "3bitr4g.mm"
include "biadan2.mm"

theorem sscoid
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ ( _I o. B ) <-> ( Rel A /\ A C_ B ) )

  proof
    cA
    cid
    cB
    ccom
    #
    wss
    #
    cA
    wrel
    #
    cA
    cB
    wss
    #
    @1
    @0
    wrel
    @2
    cid
    cB
    relco
    cA
    @0
    relss
    mpi
    @2
    vx
    cv
    #
    cA
    wcel
    #
    @4
    @0
    wcel
    #
    wi
    #
    vx
    wal
    @5
    @4
    cB
    wcel
    #
    wi
    #
    vx
    wal
    @1
    @3
    @2
    @7
    @9
    vx
    @2
    @5
    @6
    @8
    @2
    @5
    wa
    @4
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    vz
    wex
    vy
    wex
    @6
    @8
    wb
    #
    vy
    vz
    @4
    cA
    elrel
    @13
    @14
    vy
    vz
    @13
    @10
    @11
    @0
    wbr
    #
    @10
    @11
    cB
    wbr
    #
    @6
    @8
    @15
    @16
    wb
    @13
    @15
    @10
    @4
    cB
    wbr
    #
    @4
    @11
    cid
    wbr
    #
    wa
    #
    vx
    wex
    #
    @16
    vx
    @10
    @11
    cid
    cB
    vy
    vex
    vz
    vex
    #
    brco
    @20
    vx
    vz
    weq
    #
    @17
    wa
    #
    vx
    wex
    @16
    @19
    @23
    vx
    @19
    @18
    @17
    wa
    @23
    @17
    @18
    ancom
    @18
    @22
    @17
    @4
    @11
    @21
    ideq
    anbi1i
    bitri
    exbii
    @17
    @16
    vx
    @11
    @21
    @4
    @11
    @10
    cB
    breq2
    ceqsexv
    bitri
    bitri
    a1i
    @13
    @6
    @12
    @0
    wcel
    @15
    @4
    @12
    @0
    eleq1
    @10
    @11
    @0
    df-br
    syl6bbr
    @13
    @8
    @12
    cB
    wcel
    @16
    @4
    @12
    cB
    eleq1
    @10
    @11
    cB
    df-br
    syl6bbr
    3bitr4d
    exlimivv
    syl
    pm5.74da
    albidv
    vx
    cA
    @0
    dfss2
    vx
    cA
    cB
    dfss2
    3bitr4g
    biadan2
end
