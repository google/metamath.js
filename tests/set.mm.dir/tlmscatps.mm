include "ctlm.mm"
include "wcel.mm"
include "ctrg.mm"
include "ctps.mm"
include "tlmtrg.mm"
include "trgtps.mm"
include "syl.mm"

theorem tlmscatps
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


  assert |- ( W e. TopMod -> F e. TopSp )

  proof
    cW
    ctlm
    wcel
    cF
    ctrg
    wcel
    cF
    ctps
    wcel
    cF
    cW
    tlmtrg.f
    tlmtrg
    cF
    trgtps
    syl
end
