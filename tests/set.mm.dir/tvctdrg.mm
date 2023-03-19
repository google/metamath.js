include "ctvc.mm"
include "wcel.mm"
include "ctlm.mm"
include "ctdrg.mm"
include "istvc.mm"
include "simprbi.mm"

theorem tvctdrg
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


  assert |- ( W e. TopVec -> F e. TopDRing )

  proof
    cW
    ctvc
    wcel
    cW
    ctlm
    wcel
    cF
    ctdrg
    wcel
    cF
    cW
    tlmtrg.f
    istvc
    simprbi
end
