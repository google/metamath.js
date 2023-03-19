include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "ctdrg.mm"
include "wcel.mm"
include "ctlm.mm"
include "ctvc.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "df-tvc.mm"
include "elrab2.mm"

theorem istvc
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cK: class K
  let cL: class L
  let wph: wff ph
  let cX: class X
  let cY: class Y
  assume tlmtrg.f: |- F = ( Scalar ` W )


  assert |- ( W e. TopVec <-> ( W e. TopMod /\ F e. TopDRing ) )

  proof
    vx
    cv
    #
    csca
    cfv
    #
    ctdrg
    wcel
    cF
    ctdrg
    wcel
    vx
    cW
    ctlm
    ctvc
    @0
    cW
    wceq
    #
    @1
    cF
    ctdrg
    @2
    @1
    cW
    csca
    cfv
    cF
    @0
    cW
    csca
    fveq2
    tlmtrg.f
    syl6eqr
    eleq1d
    vx
    df-tvc
    elrab2
end
