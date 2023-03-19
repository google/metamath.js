include "wcel.mm"
include "wf.mm"
include "wb.mm"
include "pwselbasb.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem pwselbas
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  assume pwsbas.y: |- Y = ( R ^s I )
  assume pwsbas.f: |- B = ( Base ` R )
  assume pwselbas.v: |- V = ( Base ` Y )
  assume pwselbas.r: |- ( ph -> R e. W )
  assume pwselbas.i: |- ( ph -> I e. Z )
  assume pwselbas.x: |- ( ph -> X e. V )


  assert |- ( ph -> X : I --> B )

  proof
    wph
    cX
    cV
    wcel
    #
    cI
    cB
    cX
    wf
    #
    pwselbas.x
    wph
    cR
    cW
    wcel
    cI
    cZ
    wcel
    @0
    @1
    wb
    pwselbas.r
    pwselbas.i
    cB
    cR
    cI
    cV
    cW
    cX
    cY
    cZ
    pwsbas.y
    pwsbas.f
    pwselbas.v
    pwselbasb
    syl2anc
    mpbid
end
