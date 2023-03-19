include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ofc12.mm"
include "oveq2d.mm"
include "lflvsdi2.mm"
include "eqtr3d.mm"

theorem lflvsdi2a
  let wph: wff ph
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume lfldi.v: |- V = ( Base ` W )
  assume lfldi.r: |- R = ( Scalar ` W )
  assume lfldi.k: |- K = ( Base ` R )
  assume lfldi.p: |- .+ = ( +g ` R )
  assume lfldi.t: |- .x. = ( .r ` R )
  assume lfldi.f: |- F = ( LFnl ` W )
  assume lfldi.w: |- ( ph -> W e. LMod )
  assume lfldi.x: |- ( ph -> X e. K )
  assume lfldi2.y: |- ( ph -> Y e. K )
  assume lfldi2.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( G oF .x. ( V X. { ( X .+ Y ) } ) ) = ( ( G oF .x. ( V X. { X } ) ) oF .+ ( G oF .x. ( V X. { Y } ) ) ) )

  proof
    wph
    cG
    cV
    cX
    csn
    cxp
    #
    cV
    cY
    csn
    cxp
    #
    c.pl
    cof
    #
    co
    #
    c.x
    cof
    #
    co
    cG
    cV
    cX
    cY
    c.pl
    co
    csn
    cxp
    #
    @4
    co
    cG
    @0
    @4
    co
    cG
    @1
    @4
    co
    @2
    co
    wph
    @3
    @5
    cG
    @4
    wph
    cV
    cX
    cY
    c.pl
    cvv
    cK
    cK
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lfldi.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    lfldi.x
    lfldi2.y
    ofc12
    oveq2d
    wph
    c.pl
    cR
    c.x
    cF
    cG
    cK
    cV
    cW
    cX
    cY
    lfldi.v
    lfldi.r
    lfldi.k
    lfldi.p
    lfldi.t
    lfldi.f
    lfldi.w
    lfldi.x
    lfldi2.y
    lfldi2.g
    lflvsdi2
    eqtr3d
end
