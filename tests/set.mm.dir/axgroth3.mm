include "wel.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cdif.mm"
include "cdom.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "wex.mm"
include "axgroth2.mm"
include "cuni.mm"
include "wb.mm"
include "wcel.mm"
include "ssid.mm"
include "weq.mm"
include "sseq1.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "spv.mm"
include "mpi.mm"
include "reximi.mm"
include "eluni2.mm"
include "sylibr.mm"
include "adantl.mm"
include "ralimi.mm"
include "dfss3.mm"
include "com.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "vex.mm"
include "dominf.mm"
include "sylan.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "grothac.mm"
include "eleqtrri.mm"
include "infdif2.mm"
include "mp3an12.mm"
include "syl.mm"
include "orbi1d.mm"
include "imbi2d.mm"
include "albidv.mm"
include "sylan2.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axgroth3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  assert |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\ E. w e. y A. v ( v C_ z -> v e. w ) ) /\ A. z ( z C_ y -> ( ( y \ z ) ~<_ z \/ z e. y ) ) )

  proof
    vx
    vy
    wel
    #
    vw
    cv
    vz
    cv
    #
    wss
    vw
    vy
    wel
    wi
    vw
    wal
    #
    vv
    cv
    #
    @1
    wss
    #
    vv
    vw
    wel
    #
    wi
    #
    vv
    wal
    #
    vw
    vy
    cv
    #
    wrex
    #
    wa
    #
    vz
    @8
    wral
    #
    @1
    @8
    wss
    #
    @8
    @1
    cdif
    @1
    cdom
    wbr
    #
    vz
    vy
    wel
    #
    wo
    #
    wi
    #
    vz
    wal
    #
    w3a
    #
    vy
    wex
    @0
    @11
    @12
    @8
    @1
    cdom
    wbr
    #
    @14
    wo
    #
    wi
    #
    vz
    wal
    #
    w3a
    #
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    axgroth2
    @18
    @23
    vy
    @0
    @11
    wa
    #
    @17
    wa
    @24
    @22
    wa
    @18
    @23
    @24
    @17
    @22
    @11
    @0
    @8
    @8
    cuni
    #
    wss
    #
    @17
    @22
    wb
    @11
    @1
    @25
    wcel
    #
    vz
    @8
    wral
    @26
    @10
    @27
    vz
    @8
    @9
    @27
    @2
    @9
    vz
    vw
    wel
    #
    vw
    @8
    wrex
    @27
    @7
    @28
    vw
    @8
    @7
    @1
    @1
    wss
    #
    @28
    @1
    ssid
    @6
    @29
    @28
    wi
    vv
    vz
    vv
    vz
    weq
    @4
    @29
    @5
    @28
    @3
    @1
    @1
    sseq1
    vv
    vz
    vw
    elequ1
    imbi12d
    spv
    mpi
    reximi
    vw
    @1
    @8
    eluni2
    sylibr
    adantl
    ralimi
    vz
    @8
    @25
    dfss3
    sylibr
    @0
    @26
    wa
    #
    @16
    @21
    vz
    @30
    @15
    @20
    @12
    @30
    @13
    @19
    @14
    @30
    com
    @8
    cdom
    wbr
    #
    @13
    @19
    wb
    #
    @0
    @8
    c0
    wne
    @26
    @31
    @8
    vx
    cv
    ne0i
    @8
    vy
    vex
    #
    dominf
    sylan
    @8
    ccrd
    cdm
    #
    wcel
    @1
    @34
    wcel
    @31
    @32
    @8
    cvv
    @34
    @33
    grothac
    eleqtrri
    @1
    cvv
    @34
    vz
    vex
    grothac
    eleqtrri
    @8
    @1
    infdif2
    mp3an12
    syl
    orbi1d
    imbi2d
    albidv
    sylan2
    pm5.32i
    @0
    @11
    @17
    df-3an
    @0
    @11
    @22
    df-3an
    3bitr4i
    exbii
    mpbir
end
