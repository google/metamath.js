include "co.mm"
include "cmul.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "wcel.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchrplusg.mm"
include "oveqd.mm"
include "ofmresval.mm"
include "eqtrd.mm"

theorem dchrmul
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cB: class B
  let cK: class K
  let cL: class L
  let cU: class U
  let cA: class A
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrmul.t: |- .x. = ( +g ` G )
  assume dchrmul.x: |- ( ph -> X e. D )
  assume dchrmul.y: |- ( ph -> Y e. D )


  assert |- ( ph -> ( X .x. Y ) = ( X oF x. Y ) )

  proof
    wph
    cX
    cY
    c.x
    co
    cX
    cY
    cmul
    cof
    #
    cD
    cD
    cxp
    cres
    #
    co
    cX
    cY
    @0
    co
    wph
    c.x
    @1
    cX
    cY
    wph
    cD
    c.x
    cG
    cN
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrmul.t
    wph
    cX
    cD
    wcel
    cN
    cn
    wcel
    dchrmul.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    dchrplusg
    oveqd
    wph
    cD
    cD
    cmul
    cX
    cY
    dchrmul.x
    dchrmul.y
    ofmresval
    eqtrd
end
