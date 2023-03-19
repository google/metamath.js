include "ctsr.mm"
include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "cha.mm"
include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wbr.mm"
include "eqid.mm"
include "ordthauslem.mm"
include "necom.mm"
include "3ancoma.mm"
include "incom.mm"
include "eqeq1i.mm"
include "3anbi3i.mm"
include "bitri.mm"
include "2rexbii.mm"
include "rexcom.mm"
include "imbi12i.mm"
include "syl6ib.mm"
include "3com23.mm"
include "tsrlin.mm"
include "mpjaod.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "ctopon.mm"
include "wb.mm"
include "ordttopon.mm"
include "ishaus2.mm"
include "syl.mm"
include "mpbird.mm"

theorem ordthaus
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. TosetRel -> ( ordTop ` R ) e. Haus )

  proof
    cR
    ctsr
    wcel
    #
    cR
    cordt
    cfv
    #
    cha
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @3
    vm
    cv
    #
    wcel
    #
    @4
    vn
    cv
    #
    wcel
    #
    @6
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    @1
    wrex
    vm
    @1
    wrex
    #
    wi
    #
    vy
    cR
    cdm
    #
    wral
    vx
    @15
    wral
    #
    @0
    @14
    vx
    vy
    @15
    @15
    @0
    @3
    @15
    wcel
    #
    @4
    @15
    wcel
    #
    @14
    @0
    @17
    @18
    w3a
    @3
    @4
    cR
    wbr
    @14
    @4
    @3
    cR
    wbr
    #
    @3
    @4
    cR
    vm
    vn
    @15
    @15
    eqid
    #
    ordthauslem
    @0
    @18
    @17
    @19
    @14
    wi
    @0
    @18
    @17
    w3a
    @19
    @4
    @3
    wne
    #
    @9
    @7
    @8
    @6
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vm
    @1
    wrex
    vn
    @1
    wrex
    #
    wi
    @14
    @4
    @3
    cR
    vn
    vm
    @15
    @20
    ordthauslem
    @21
    @5
    @25
    @13
    @4
    @3
    necom
    @25
    @12
    vm
    @1
    wrex
    vn
    @1
    wrex
    @13
    @24
    @12
    vn
    vm
    @1
    @1
    @24
    @7
    @9
    @23
    w3a
    @12
    @9
    @7
    @23
    3ancoma
    @23
    @11
    @7
    @9
    @22
    @10
    c0
    @8
    @6
    incom
    eqeq1i
    3anbi3i
    bitri
    2rexbii
    @12
    vn
    vm
    @1
    @1
    rexcom
    bitri
    imbi12i
    syl6ib
    3com23
    @3
    @4
    cR
    @15
    @20
    tsrlin
    mpjaod
    3expb
    ralrimivva
    @0
    @1
    @15
    ctopon
    cfv
    wcel
    @2
    @16
    wb
    cR
    ctsr
    @15
    @20
    ordttopon
    vx
    vy
    vn
    vm
    @1
    @15
    ishaus2
    syl
    mpbird
end
