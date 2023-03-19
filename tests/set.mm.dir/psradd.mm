include "co.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "psrplusg.mm"
include "oveqi.mm"
include "ofmresval.mm"
include "syl5eq.mm"

theorem psradd
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let cI: class I
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let vh: setvar h
  let vy: setvar y
  assume psrplusg.s: |- S = ( I mPwSer R )
  assume psrplusg.b: |- B = ( Base ` S )
  assume psrplusg.a: |- .+ = ( +g ` R )
  assume psrplusg.p: |- .+b = ( +g ` S )
  assume psradd.x: |- ( ph -> X e. B )
  assume psradd.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .+b Y ) = ( X oF .+ Y ) )

  proof
    wph
    cX
    cY
    c.pb
    co
    cX
    cY
    c.pl
    cof
    #
    cB
    cB
    cxp
    cres
    #
    co
    cX
    cY
    @0
    co
    c.pb
    @1
    cX
    cY
    cB
    c.pl
    c.pb
    cR
    cS
    cI
    psrplusg.s
    psrplusg.b
    psrplusg.a
    psrplusg.p
    psrplusg
    oveqi
    wph
    cB
    cB
    c.pl
    cX
    cY
    psradd.x
    psradd.y
    ofmresval
    syl5eq
end
