include "cco.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfunc.mm"
include "co.mm"
include "ccofu.mm"
include "cmpt2.mm"
include "ctp.mm"
include "catcbas.mm"
include "eqid.mm"
include "catchomfval.mm"
include "eqidd.mm"
include "catcval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "catstr.mm"
include "ccoid.mm"
include "snsstp3.mm"
include "strfv.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem catccofval
  let wph: wff ph
  let vz: setvar z
  let vv: setvar v
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cF: class F
  let cG: class G
  let cY: class Y
  let cZ: class Z
  assume catcbas.c: |- C = ( CatCat ` U )
  assume catcbas.b: |- B = ( Base ` C )
  assume catcbas.u: |- ( ph -> U e. V )
  assume catcco.o: |- .x. = ( comp ` C )

  disjoint v z
  disjoint B v
  disjoint B z
  disjoint f g
  disjoint f v
  disjoint f z
  disjoint f ph
  disjoint g v
  disjoint g z
  disjoint g ph
  disjoint ph v
  disjoint ph z
  disjoint U v
  disjoint U z
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint ph x
  disjoint ph y
  disjoint U x
  disjoint U y
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
  assert |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |-> ( g e. ( ( 2nd ` v ) Func z ) , f e. ( Func ` v ) |-> ( g o.func f ) ) ) )

  proof
    wph
    cC
    cco
    cfv
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    chom
    cfv
    cC
    chom
    cfv
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
    #
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
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    cco
    cfv
    #
    c.x
    @6
    wph
    cC
    @8
    cco
    wph
    vx
    vy
    vz
    vv
    cB
    cC
    @6
    cU
    vf
    vg
    @1
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
    vx
    vy
    cB
    cC
    cU
    @1
    cV
    catcbas.c
    catcbas.b
    catcbas.u
    @1
    eqid
    catchomfval
    wph
    @6
    eqidd
    catcval
    fveq2d
    catcco.o
    @6
    cvv
    wcel
    @6
    @9
    wceq
    vv
    vz
    @3
    cB
    @5
    cB
    cB
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
    @10
    xpex
    @10
    mpt2ex
    @6
    @8
    cco
    cvv
    c1
    c1
    c5
    cdc
    cop
    @6
    cB
    @1
    catstr
    ccoid
    @0
    @2
    @7
    snsstp3
    strfv
    ax-mp
    3eqtr4g
end
