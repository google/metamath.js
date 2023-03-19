include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "cxp.mm"
include "prdsle.mm"
include "wcel.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "opabssxp.mm"
include "eqsstr3i.mm"
include "syl6eqss.mm"

theorem prdsless
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cI: class I
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cH: class H
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume prdsbas.p: |- P = ( S Xs_ R )
  assume prdsbas.s: |- ( ph -> S e. V )
  assume prdsbas.r: |- ( ph -> R e. W )
  assume prdsbas.b: |- B = ( Base ` P )
  assume prdsbas.i: |- ( ph -> dom R = I )
  assume prdsle.l: |- .<_ = ( le ` P )


  assert |- ( ph -> .<_ C_ ( B X. B ) )

  proof
    wph
    c.le
    vf
    cv
    #
    vg
    cv
    #
    cpr
    cB
    wss
    #
    vx
    cv
    #
    @0
    cfv
    @3
    @1
    cfv
    @3
    cR
    cfv
    cple
    cfv
    wbr
    vx
    cI
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    cB
    cB
    cxp
    #
    wph
    vx
    cB
    cP
    cR
    cS
    vf
    vg
    cI
    c.le
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    prdsle.l
    prdsle
    @6
    @0
    cB
    wcel
    @1
    cB
    wcel
    wa
    #
    @4
    wa
    #
    vf
    vg
    copab
    @7
    @9
    @5
    vf
    vg
    @8
    @2
    @4
    @0
    @1
    cB
    vf
    vex
    vg
    vex
    prss
    anbi1i
    opabbii
    @4
    vf
    vg
    cB
    cB
    opabssxp
    eqsstr3i
    syl6eqss
end
