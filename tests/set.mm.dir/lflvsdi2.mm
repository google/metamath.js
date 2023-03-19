include "csn.mm"
include "cxp.mm"
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
include "co.mm"
include "wceq.mm"
include "lmodring.mm"
include "ringdi.mm"
include "sylan.mm"
include "caofdi.mm"

theorem lflvsdi2
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


  assert |- ( ph -> ( G oF .x. ( ( V X. { X } ) oF .+ ( V X. { Y } ) ) ) = ( ( G oF .x. ( V X. { X } ) ) oF .+ ( G oF .x. ( V X. { Y } ) ) ) )

  proof
    wph
    vx
    vy
    vz
    cV
    c.pl
    cK
    c.x
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
    cK
    c.pl
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
    lfldi.v
    cW
    cbs
    fvex
    eqeltri
    a1i
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
    lfldi.w
    lfldi2.g
    cR
    cF
    cG
    cK
    cV
    cW
    clmod
    lfldi.r
    lfldi.k
    lfldi.v
    lfldi.f
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
    lfldi.x
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
    @1
    wf
    lfldi2.y
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
    @4
    @5
    @6
    c.pl
    co
    c.x
    co
    @4
    @5
    c.x
    co
    @4
    @6
    c.x
    co
    c.pl
    co
    wceq
    wph
    @2
    @3
    lfldi.w
    cR
    cW
    lfldi.r
    lmodring
    syl
    cK
    c.pl
    cR
    c.x
    @4
    @5
    @6
    lfldi.k
    lfldi.p
    lfldi.t
    ringdi
    sylan
    caofdi
end
