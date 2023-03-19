include "ctpos.mm"
include "cdm.mm"
include "wrel.mm"
include "ccnv.mm"
include "wa.mm"
include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "0nelxp.mm"
include "ssel.mm"
include "mtoi.mm"
include "df-rel.mm"
include "reldmtpos.mm"
include "3imtr4i.mm"
include "relcnv.mm"
include "jctir.mm"
include "cv.mm"
include "cop.mm"
include "wbr.mm"
include "wex.mm"
include "wb.mm"
include "vex.mm"
include "brtpos.mm"
include "mp1i.mm"
include "exbidv.mm"
include "opex.mm"
include "eldm.mm"
include "opelcnv.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "eqrelrdv2.mm"
include "mpancom.mm"

theorem dmtpos
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel dom F -> dom tpos F = `' dom F )

  proof
    cF
    ctpos
    #
    cdm
    #
    wrel
    #
    cF
    cdm
    #
    ccnv
    #
    wrel
    #
    wa
    @3
    wrel
    #
    @1
    @4
    wceq
    @6
    @2
    @5
    @3
    cvv
    cvv
    cxp
    #
    wss
    #
    c0
    @3
    wcel
    #
    wn
    @6
    @2
    @8
    @9
    c0
    @7
    wcel
    cvv
    cvv
    0nelxp
    @3
    @7
    c0
    ssel
    mtoi
    @3
    df-rel
    cF
    reldmtpos
    3imtr4i
    @3
    relcnv
    jctir
    @6
    vx
    vy
    @1
    @4
    @6
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    @0
    wbr
    #
    vz
    wex
    @11
    @10
    cop
    #
    @13
    cF
    wbr
    #
    vz
    wex
    #
    @12
    @1
    wcel
    @12
    @4
    wcel
    #
    @6
    @14
    @16
    vz
    @13
    cvv
    wcel
    @14
    @16
    wb
    @6
    vz
    vex
    @10
    @11
    @13
    cF
    cvv
    brtpos
    mp1i
    exbidv
    vz
    @12
    @0
    @10
    @11
    opex
    eldm
    @18
    @15
    @3
    wcel
    @17
    @10
    @11
    @3
    vx
    vex
    vy
    vex
    opelcnv
    vz
    @15
    cF
    @11
    @10
    opex
    eldm
    bitri
    3bitr4g
    eqrelrdv2
    mpancom
end
