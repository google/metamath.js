include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cpw.mm"
include "crab.mm"
include "sprval.mm"
include "wa.mm"
include "wb.mm"
include "wss.mm"
include "prssi.mm"
include "eleq1.mm"
include "prex.mm"
include "elpw.mm"
include "syl6bb.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "pm4.71ri.mm"
include "a1i.mm"
include "abbidv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "eqtrd.mm"

theorem sprvalpw
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x

  disjoint V a
  disjoint V b
  disjoint V p
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint k x
  assert |- ( V e. W -> ( Pairs ` V ) = { p e. ~P V | E. a e. V E. b e. V p = { a , b } } )

  proof
    cV
    cW
    wcel
    #
    cV
    cspr
    cfv
    vp
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    vp
    cab
    #
    @6
    vp
    cV
    cpw
    #
    crab
    #
    cV
    cW
    vp
    va
    vb
    sprval
    @0
    @7
    @1
    @8
    wcel
    #
    @6
    wa
    #
    vp
    cab
    @9
    @0
    @6
    @11
    vp
    @6
    @11
    wb
    @0
    @6
    @10
    @5
    @10
    va
    vb
    cV
    cV
    @2
    cV
    wcel
    @3
    cV
    wcel
    wa
    @10
    @5
    @4
    cV
    wss
    #
    @2
    @3
    cV
    prssi
    @5
    @10
    @4
    @8
    wcel
    @12
    @1
    @4
    @8
    eleq1
    @4
    cV
    @2
    @3
    prex
    elpw
    syl6bb
    syl5ibrcom
    rexlimivv
    pm4.71ri
    a1i
    abbidv
    @6
    vp
    @8
    df-rab
    syl6eqr
    eqtrd
end
