include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cmul.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "cpr.mm"
include "cui.mm"
include "eqid.mm"
include "dchrbas.mm"
include "dchrval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "ofexg.mm"
include "grpplusg.mm"
include "mp2b.mm"
include "3eqtr4g.mm"

theorem dchrplusg
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let cG: class G
  let cN: class N
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
  let cX: class X
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrmul.t: |- .x. = ( +g ` G )
  assume dchrplusg.n: |- ( ph -> N e. NN )


  assert |- ( ph -> .x. = ( oF x. |` ( D X. D ) ) )

  proof
    wph
    cG
    cplusg
    cfv
    cnx
    cbs
    cfv
    cD
    cop
    cnx
    cplusg
    cfv
    cmul
    cof
    cD
    cD
    cxp
    #
    cres
    #
    cop
    cpr
    #
    cplusg
    cfv
    #
    c.x
    @1
    wph
    cG
    @2
    cplusg
    wph
    vx
    cZ
    cbs
    cfv
    #
    cD
    cZ
    cui
    cfv
    #
    cG
    cN
    cZ
    dchrmhm.g
    dchrmhm.z
    @4
    eqid
    #
    @5
    eqid
    #
    dchrplusg.n
    wph
    vx
    @4
    cD
    @5
    cG
    cN
    cZ
    dchrmhm.g
    dchrmhm.z
    @6
    @7
    dchrplusg.n
    dchrmhm.b
    dchrbas
    dchrval
    fveq2d
    dchrmul.t
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @1
    @3
    wceq
    cD
    cD
    cD
    cG
    cbs
    cfv
    cvv
    dchrmhm.b
    cG
    cbs
    fvex
    eqeltri
    #
    @8
    xpex
    @0
    cmul
    cvv
    ofexg
    cD
    @1
    @2
    cvv
    @2
    eqid
    grpplusg
    mp2b
    3eqtr4g
end
