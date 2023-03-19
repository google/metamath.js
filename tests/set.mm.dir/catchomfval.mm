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
include "catcbas.mm"
include "eqidd.mm"
include "catcval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "catstr.mm"
include "homid.mm"
include "snsstp2.mm"
include "strfv.mm"
include "mp1i.mm"
include "eqtr4d.mm"

theorem catchomfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vv: setvar v
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
  assume catchomfval.h: |- H = ( Hom ` C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint U x
  disjoint U y
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint f g
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f ph
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g ph
  disjoint ph v
  disjoint ph z
  disjoint U v
  disjoint U z
  disjoint X f
  disjoint X g
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint Y f
  disjoint Y g
  disjoint Y v
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z f
  disjoint Z g
  disjoint Z v
  disjoint Z z
  assert |- ( ph -> H = ( x e. B , y e. B |-> ( x Func y ) ) )

  proof
    wph
    cH
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    chom
    cfv
    vx
    vy
    cB
    cB
    vx
    cv
    vy
    cv
    cfunc
    co
    #
    cmpt2
    #
    cop
    #
    cnx
    cco
    cfv
    vv
    vz
    cB
    cB
    cxp
    cB
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
    #
    chom
    cfv
    #
    @2
    wph
    cH
    cC
    chom
    cfv
    @8
    catchomfval.h
    wph
    cC
    @7
    chom
    wph
    vx
    vy
    vz
    vv
    cB
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
    cB
    cC
    cU
    cV
    catcbas.c
    catcbas.b
    catcbas.u
    catcbas
    wph
    @2
    eqidd
    wph
    @5
    eqidd
    catcval
    fveq2d
    syl5eq
    @2
    cvv
    wcel
    @2
    @8
    wceq
    wph
    vx
    vy
    cB
    cB
    @1
    cB
    cC
    cbs
    cfv
    cvv
    catcbas.b
    cC
    cbs
    fvex
    eqeltri
    #
    @9
    mpt2ex
    @2
    @7
    chom
    cvv
    c1
    c1
    c5
    cdc
    cop
    @5
    cB
    @2
    catstr
    homid
    @0
    @3
    @6
    snsstp2
    strfv
    mp1i
    eqtr4d
end
