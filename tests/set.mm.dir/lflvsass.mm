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
include "clmod.mm"
include "wf.mm"
include "lflf.mm"
include "syl2anc.mm"
include "fconst6g.mm"
include "syl.mm"
include "crg.mm"
include "cv.mm"
include "w3a.mm"
include "wceq.mm"
include "lmodring.mm"
include "ringass.mm"
include "sylan.mm"
include "caofass.mm"
include "ofc12.mm"
include "oveq2d.mm"
include "eqtr2d.mm"

theorem lflvsass
  let wph: wff ph
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
  assume lflass.v: |- V = ( Base ` W )
  assume lflass.r: |- R = ( Scalar ` W )
  assume lflass.k: |- K = ( Base ` R )
  assume lflass.t: |- .x. = ( .r ` R )
  assume lflass.f: |- F = ( LFnl ` W )
  assume lflass.w: |- ( ph -> W e. LMod )
  assume lflass.x: |- ( ph -> X e. K )
  assume lflass.y: |- ( ph -> Y e. K )
  assume lflass.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( G oF .x. ( V X. { ( X .x. Y ) } ) ) = ( ( G oF .x. ( V X. { X } ) ) oF .x. ( V X. { Y } ) ) )

  proof
    wph
    cG
    cV
    cX
    csn
    cxp
    #
    c.x
    cof
    #
    co
    cV
    cY
    csn
    cxp
    #
    @1
    co
    cG
    @0
    @2
    @1
    co
    #
    @1
    co
    cG
    cV
    cX
    cY
    c.x
    co
    csn
    cxp
    #
    @1
    co
    wph
    vx
    vy
    vz
    cV
    c.x
    c.x
    cK
    c.x
    cG
    @0
    @2
    c.x
    cvv
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lflass.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    #
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    cV
    cK
    cG
    wf
    lflass.w
    lflass.g
    cR
    cF
    cG
    cK
    cV
    cW
    clmod
    lflass.r
    lflass.k
    lflass.v
    lflass.f
    lflf
    syl2anc
    wph
    cX
    cK
    wcel
    cV
    cK
    @0
    wf
    lflass.x
    cV
    cX
    cK
    fconst6g
    syl
    wph
    cY
    cK
    wcel
    cV
    cK
    @2
    wf
    lflass.y
    cV
    cY
    cK
    fconst6g
    syl
    wph
    cR
    crg
    wcel
    #
    vx
    cv
    #
    cK
    wcel
    vy
    cv
    #
    cK
    wcel
    vz
    cv
    #
    cK
    wcel
    w3a
    @8
    @9
    c.x
    co
    @10
    c.x
    co
    @8
    @9
    @10
    c.x
    co
    c.x
    co
    wceq
    wph
    @6
    @7
    lflass.w
    cR
    cW
    lflass.r
    lmodring
    syl
    cK
    cR
    c.x
    @8
    @9
    @10
    lflass.k
    lflass.t
    ringass
    sylan
    caofass
    wph
    @3
    @4
    cG
    @1
    wph
    cV
    cX
    cY
    c.x
    cvv
    cK
    cK
    @5
    lflass.x
    lflass.y
    ofc12
    oveq2d
    eqtr2d
end
