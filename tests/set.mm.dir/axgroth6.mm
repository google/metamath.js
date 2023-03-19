include "wel.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "csdm.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "wex.mm"
include "wrex.mm"
include "cen.mm"
include "wo.mm"
include "axgroth5.mm"
include "biid.mm"
include "wb.mm"
include "wceq.mm"
include "pweq.mm"
include "sseq1d.mm"
include "cbvralv.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "rspccv.mm"
include "wal.mm"
include "pwss.mm"
include "vpwex.mm"
include "sseq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylbi.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "impbid2.mm"
include "ralbidv.mm"
include "pm5.32i.mm"
include "r19.26.mm"
include "3bitr4i.mm"
include "selpw.mm"
include "wn.mm"
include "cdom.mm"
include "impexp.mm"
include "cvv.mm"
include "vex.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "pm4.71i.mm"
include "imbi1i.mm"
include "brsdom.mm"
include "bitri.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"
include "pm5.74ri.mm"
include "pm4.64.mm"
include "syl6bb.mm"
include "ralbiia.mm"
include "3anbi123i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axgroth6
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  assert |- E. y ( x e. y /\ A. z e. y ( ~P z C_ y /\ ~P z e. y ) /\ A. z e. ~P y ( z ~< y -> z e. y ) )

  proof
    vx
    vy
    wel
    #
    vz
    cv
    #
    cpw
    #
    vy
    cv
    #
    wss
    #
    @2
    @3
    wcel
    #
    wa
    vz
    @3
    wral
    #
    @1
    @3
    csdm
    wbr
    #
    vz
    vy
    wel
    #
    wi
    #
    vz
    @3
    cpw
    #
    wral
    #
    w3a
    #
    vy
    wex
    @0
    @4
    @2
    vw
    cv
    #
    wss
    #
    vw
    @3
    wrex
    #
    wa
    vz
    @3
    wral
    #
    @1
    @3
    cen
    wbr
    #
    @8
    wo
    #
    vz
    @10
    wral
    #
    w3a
    #
    vy
    wex
    vx
    vy
    vz
    vw
    axgroth5
    @12
    @20
    vy
    @0
    @0
    @6
    @16
    @11
    @19
    @0
    biid
    @4
    vz
    @3
    wral
    #
    @5
    vz
    @3
    wral
    #
    wa
    @21
    @15
    vz
    @3
    wral
    #
    wa
    @6
    @16
    @21
    @22
    @23
    @21
    vv
    cv
    #
    cpw
    #
    @3
    wss
    #
    vv
    @3
    wral
    #
    @22
    @23
    wb
    @4
    @26
    vz
    vv
    @3
    @1
    @24
    wceq
    @2
    @25
    @3
    @1
    @24
    pweq
    sseq1d
    cbvralv
    @27
    @5
    @15
    vz
    @3
    @27
    @5
    @15
    @5
    @2
    @2
    wss
    #
    @15
    @2
    ssid
    @14
    @28
    vw
    @2
    @3
    @13
    @2
    @2
    sseq2
    rspcev
    mpan2
    @27
    @14
    @5
    vw
    @3
    @27
    vw
    vy
    wel
    @13
    cpw
    #
    @3
    wss
    #
    @14
    @5
    wi
    #
    @26
    @30
    vv
    @13
    @3
    @24
    @13
    wceq
    @25
    @29
    @3
    @24
    @13
    pweq
    sseq1d
    rspccv
    @30
    @24
    @13
    wss
    #
    vv
    vy
    wel
    #
    wi
    #
    vv
    wal
    @31
    vv
    @13
    @3
    pwss
    @34
    @31
    vv
    @2
    vz
    vpwex
    @24
    @2
    wceq
    @32
    @14
    @33
    @5
    @24
    @2
    @13
    sseq1
    @24
    @2
    @3
    eleq1
    imbi12d
    spcv
    sylbi
    syl6
    rexlimdv
    impbid2
    ralbidv
    sylbi
    pm5.32i
    @4
    @5
    vz
    @3
    r19.26
    @4
    @15
    vz
    @3
    r19.26
    3bitr4i
    @9
    @18
    vz
    @10
    @1
    @10
    wcel
    @1
    @3
    wss
    #
    @9
    @18
    wb
    vz
    @3
    selpw
    @35
    @9
    @17
    wn
    #
    @8
    wi
    #
    @18
    @35
    @9
    @37
    @35
    @1
    @3
    cdom
    wbr
    #
    wa
    #
    @37
    wi
    @35
    @38
    @37
    wi
    #
    wi
    @35
    @37
    wi
    @35
    @9
    wi
    @35
    @38
    @37
    impexp
    @35
    @39
    @37
    @35
    @38
    @3
    cvv
    wcel
    @35
    @38
    wi
    vy
    vex
    @1
    @3
    cvv
    ssdomg
    ax-mp
    pm4.71i
    imbi1i
    @9
    @40
    @35
    @9
    @38
    @36
    wa
    #
    @8
    wi
    @40
    @7
    @41
    @8
    @1
    @3
    brsdom
    imbi1i
    @38
    @36
    @8
    impexp
    bitri
    imbi2i
    3bitr4ri
    pm5.74ri
    @17
    @8
    pm4.64
    syl6bb
    sylbi
    ralbiia
    3anbi123i
    exbii
    mpbir
end
