include "cv.mm"
include "cdm.mm"
include "cxp.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "cps.mm"
include "ctsr.mm"
include "wceq.mm"
include "dmeq.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "id.mm"
include "cnveq.mm"
include "uneq12d.mm"
include "sseq12d.mm"
include "df-tsr.mm"
include "elrab2.mm"

theorem istsr
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vr: setvar r
  assume istsr.1: |- X = dom R


  assert |- ( R e. TosetRel <-> ( R e. PosetRel /\ ( X X. X ) C_ ( R u. `' R ) ) )

  proof
    vr
    cv
    #
    cdm
    #
    @1
    cxp
    #
    @0
    @0
    ccnv
    #
    cun
    #
    wss
    cX
    cX
    cxp
    #
    cR
    cR
    ccnv
    #
    cun
    #
    wss
    vr
    cR
    cps
    ctsr
    @0
    cR
    wceq
    #
    @2
    @5
    @4
    @7
    @8
    @1
    cX
    @8
    @1
    cR
    cdm
    cX
    @0
    cR
    dmeq
    istsr.1
    syl6eqr
    sqxpeqd
    @8
    @0
    cR
    @3
    @6
    @8
    id
    @0
    cR
    cnveq
    uneq12d
    sseq12d
    vr
    df-tsr
    elrab2
end
