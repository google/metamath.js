include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cple.mm"
include "wbr.mm"
include "cbs.mm"
include "crab.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "diafn.mm"
include "fvelrnb.mm"
include "syl.mm"
include "wi.mm"
include "breq1.mm"
include "elrab.mm"
include "diass.mm"
include "ex.mm"
include "sseq1.mm"
include "biimpcd.mm"
include "syl6.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "imp.mm"

theorem diaelrnN
  let cS: class S
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume diaelrn.h: |- H = ( LHyp ` K )
  assume diaelrn.t: |- T = ( ( LTrn ` K ) ` W )
  assume diaelrn.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ S e. ran I ) -> S C_ T )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cI
    crn
    wcel
    #
    cS
    cT
    wss
    #
    @0
    @1
    vx
    cv
    #
    cI
    cfv
    #
    cS
    wceq
    #
    vx
    vy
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    vy
    cK
    cbs
    cfv
    #
    crab
    #
    wrex
    #
    @2
    @0
    cI
    @10
    wfn
    @1
    @11
    wb
    vy
    @9
    cH
    cI
    cK
    @7
    cV
    cW
    @9
    eqid
    #
    @7
    eqid
    #
    diaelrn.h
    diaelrn.i
    diafn
    vx
    @10
    cS
    cI
    fvelrnb
    syl
    @0
    @5
    @2
    vx
    @10
    @3
    @10
    wcel
    @3
    @9
    wcel
    @3
    cW
    @7
    wbr
    #
    wa
    #
    @0
    @5
    @2
    wi
    #
    @8
    @14
    vy
    @3
    @9
    @6
    @3
    cW
    @7
    breq1
    elrab
    @0
    @15
    @4
    cT
    wss
    #
    @16
    @0
    @15
    @17
    @9
    cT
    cH
    cI
    cK
    @7
    cV
    cW
    @3
    @12
    @13
    diaelrn.h
    diaelrn.t
    diaelrn.i
    diass
    ex
    @5
    @17
    @2
    @4
    cS
    cT
    sseq1
    biimpcd
    syl6
    syl5bi
    rexlimdv
    sylbid
    imp
end
