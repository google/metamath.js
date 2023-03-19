include "clmod.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "sylan.mm"
include "inidm.mm"
include "off.mm"

theorem lcomf
  let wph: wff ph
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume lcomf.f: |- F = ( Scalar ` W )
  assume lcomf.k: |- K = ( Base ` F )
  assume lcomf.s: |- .x. = ( .s ` W )
  assume lcomf.b: |- B = ( Base ` W )
  assume lcomf.w: |- ( ph -> W e. LMod )
  assume lcomf.g: |- ( ph -> G : I --> K )
  assume lcomf.h: |- ( ph -> H : I --> B )
  assume lcomf.i: |- ( ph -> I e. V )


  assert |- ( ph -> ( G oF .x. H ) : I --> B )

  proof
    wph
    vx
    vy
    cI
    cI
    cI
    c.x
    cK
    cB
    cB
    cG
    cH
    cV
    cV
    wph
    cW
    clmod
    wcel
    #
    vx
    cv
    #
    cK
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    @1
    @3
    c.x
    co
    cB
    wcel
    #
    lcomf.w
    @0
    @2
    @4
    @5
    @1
    c.x
    cF
    cK
    cB
    cW
    @3
    lcomf.b
    lcomf.f
    lcomf.s
    lcomf.k
    lmodvscl
    3expb
    sylan
    lcomf.g
    lcomf.h
    lcomf.i
    lcomf.i
    cI
    inidm
    off
end
