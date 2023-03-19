include "ccmn.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cabl.mm"
include "ablcmn.mm"
include "syl.mm"
include "cmn32.mm"
include "syl13anc.mm"

theorem abl32
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cW: class W
  assume ablcom.b: |- B = ( Base ` G )
  assume ablcom.p: |- .+ = ( +g ` G )
  assume abl32.g: |- ( ph -> G e. Abel )
  assume abl32.x: |- ( ph -> X e. B )
  assume abl32.y: |- ( ph -> Y e. B )
  assume abl32.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( ( X .+ Y ) .+ Z ) = ( ( X .+ Z ) .+ Y ) )

  proof
    wph
    cG
    ccmn
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    cX
    cZ
    c.pl
    co
    cY
    c.pl
    co
    wceq
    wph
    cG
    cabl
    wcel
    @0
    abl32.g
    cG
    ablcmn
    syl
    abl32.x
    abl32.y
    abl32.z
    cB
    c.pl
    cG
    cX
    cY
    cZ
    ablcom.b
    ablcom.p
    cmn32
    syl13anc
end
