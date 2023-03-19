include "ctlm.mm"
include "wcel.mm"
include "ctmd.mm"
include "clmod.mm"
include "ctrg.mm"
include "w3a.mm"
include "cscaf.mm"
include "cfv.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "eqid.mm"
include "istlm.mm"
include "simplbi.mm"
include "simp3d.mm"

theorem tlmtrg
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


  assert |- ( W e. TopMod -> F e. TopRing )

  proof
    cW
    ctlm
    wcel
    #
    cW
    ctmd
    wcel
    #
    cW
    clmod
    wcel
    #
    cF
    ctrg
    wcel
    #
    @0
    @1
    @2
    @3
    w3a
    cW
    cscaf
    cfv
    #
    cF
    ctopn
    cfv
    #
    cW
    ctopn
    cfv
    #
    ctx
    co
    @6
    ccn
    co
    wcel
    @4
    cF
    @6
    @5
    cW
    @4
    eqid
    @6
    eqid
    tlmtrg.f
    @5
    eqid
    istlm
    simplbi
    simp3d
end
