include "ccat.mm"
include "cin.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "chom.mm"
include "cv.mm"
include "cfunc.mm"
include "co.mm"
include "cmpt2.mm"
include "cco.mm"
include "cxp.mm"
include "c2nd.mm"
include "ccofu.mm"
include "ctp.mm"
include "cvv.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqidd.mm"
include "catcval.mm"
include "catstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "wcel.mm"
include "inex1g.mm"
include "syl.mm"
include "strfv3.mm"

theorem catcbas
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let cX: class X
  let cF: class F
  let cG: class G
  let cY: class Y
  let cZ: class Z
  assume catcbas.c: |- C = ( CatCat ` U )
  assume catcbas.b: |- B = ( Base ` C )
  assume catcbas.u: |- ( ph -> U e. V )


  assert |- ( ph -> B = ( U i^i Cat ) )

  proof
    wph
    cB
    cU
    ccat
    cin
    #
    cnx
    cbs
    cfv
    @0
    cop
    #
    cnx
    chom
    cfv
    vx
    vy
    @0
    @0
    vx
    cv
    vy
    cv
    cfunc
    co
    cmpt2
    #
    cop
    #
    cnx
    cco
    cfv
    vv
    vz
    @0
    @0
    cxp
    @0
    vg
    vf
    vv
    cv
    #
    c2nd
    cfv
    vz
    cv
    cfunc
    co
    @4
    cfunc
    cfv
    vg
    cv
    vf
    cv
    ccofu
    co
    cmpt2
    cmpt2
    #
    cop
    #
    ctp
    cC
    cbs
    cvv
    c1
    c1
    c5
    cdc
    cop
    wph
    vx
    vy
    vz
    vv
    @0
    cC
    @5
    cU
    vf
    vg
    @2
    cV
    catcbas.c
    catcbas.u
    wph
    @0
    eqidd
    wph
    @2
    eqidd
    wph
    @5
    eqidd
    catcval
    @5
    @0
    @2
    catstr
    baseid
    @1
    @3
    @6
    snsstp1
    wph
    cU
    cV
    wcel
    @0
    cvv
    wcel
    catcbas.u
    cU
    ccat
    cV
    inex1g
    syl
    catcbas.b
    strfv3
end
