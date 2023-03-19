include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cui.mm"
include "wral.mm"
include "cur.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "wcel.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "eqid.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchrelbas3.mm"
include "mpbid.mm"
include "simpld.mm"

theorem dchrf
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cK: class K
  let cL: class L
  let cU: class U
  let cA: class A
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrf.b: |- B = ( Base ` Z )
  assume dchrf.x: |- ( ph -> X e. D )


  assert |- ( ph -> X : B --> CC )

  proof
    wph
    cB
    cc
    cX
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cZ
    cmulr
    cfv
    co
    cX
    cfv
    @1
    cX
    cfv
    #
    @2
    cX
    cfv
    cmul
    co
    wceq
    vy
    cZ
    cui
    cfv
    #
    wral
    vx
    @4
    wral
    cZ
    cur
    cfv
    cX
    cfv
    c1
    wceq
    @3
    cc0
    wne
    @1
    @4
    wcel
    wi
    vx
    cB
    wral
    w3a
    #
    wph
    cX
    cD
    wcel
    #
    @0
    @5
    wa
    dchrf.x
    wph
    vx
    vy
    cB
    cD
    @4
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrf.b
    @4
    eqid
    wph
    @6
    cN
    cn
    wcel
    dchrf.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    dchrmhm.b
    dchrelbas3
    mpbid
    simpld
end
