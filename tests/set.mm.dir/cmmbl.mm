include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cdif.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "difssd.mm"
include "elpwi.mm"
include "w3a.mm"
include "inss1.mm"
include "ovolsscl.mm"
include "mp3an1.mm"
include "3adant1.mm"
include "recnd.mm"
include "difss.mm"
include "addcomd.mm"
include "mblsplit.mm"
include "indifcom.mm"
include "simp2.mm"
include "ssdifssd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "difin.mm"
include "difeq2d.mm"
include "dfin4.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "3expia.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "ismbl.mm"
include "sylanbrc.mm"

theorem cmmbl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( A e. dom vol -> ( RR \ A ) e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cr
    cA
    cdif
    #
    cr
    wss
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @4
    @3
    @2
    cin
    #
    covol
    cfv
    #
    @3
    @2
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    @2
    @0
    wcel
    @1
    cr
    cA
    difssd
    @1
    @12
    vx
    @13
    @3
    @13
    wcel
    @1
    @3
    cr
    wss
    #
    @12
    @3
    cr
    elpwi
    @1
    @14
    @5
    @11
    @1
    @14
    @5
    w3a
    #
    @3
    cA
    cin
    #
    covol
    cfv
    #
    @3
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    @19
    @17
    caddc
    co
    @4
    @10
    @15
    @17
    @19
    @15
    @17
    @14
    @5
    @17
    cr
    wcel
    #
    @1
    @16
    @3
    wss
    @14
    @5
    @20
    @3
    cA
    inss1
    @16
    @3
    ovolsscl
    mp3an1
    3adant1
    recnd
    @15
    @19
    @14
    @5
    @19
    cr
    wcel
    #
    @1
    @18
    @3
    wss
    @14
    @5
    @21
    @3
    cA
    difss
    @18
    @3
    ovolsscl
    mp3an1
    3adant1
    recnd
    addcomd
    cA
    @3
    mblsplit
    @15
    @7
    @19
    @9
    @17
    caddc
    @15
    @6
    @18
    covol
    @15
    @6
    cr
    @18
    cin
    #
    @18
    cr
    @3
    cA
    indifcom
    @15
    @18
    cr
    wss
    @22
    @18
    wceq
    @15
    @3
    cr
    cA
    @1
    @14
    @5
    simp2
    ssdifssd
    @18
    cr
    sseqin2
    sylib
    syl5eqr
    #
    fveq2d
    @15
    @8
    @16
    covol
    @15
    @8
    @3
    @18
    cdif
    #
    @16
    @15
    @8
    @3
    @6
    cdif
    @24
    @3
    @2
    difin
    @15
    @6
    @18
    @3
    @23
    difeq2d
    syl5eqr
    @3
    cA
    dfin4
    syl6eqr
    fveq2d
    oveq12d
    3eqtr4d
    3expia
    sylan2
    ralrimiva
    vx
    @2
    ismbl
    sylanbrc
end
