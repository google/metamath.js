include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "c1st.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cvv.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqid.mm"
include "setchomfval.mm"
include "eqidd.mm"
include "setcval.mm"
include "catstr.mm"
include "ccoid.mm"
include "snsstp3.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "mpt2exga.mm"
include "strfv3.mm"

theorem setccofval
  let wph: wff ph
  let vz: setvar z
  let vv: setvar v
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  let cG: class G
  let cZ: class Z
  assume setcbas.c: |- C = ( SetCat ` U )
  assume setcbas.u: |- ( ph -> U e. V )
  assume setcco.o: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f v
  disjoint f z
  disjoint f ph
  disjoint g v
  disjoint g z
  disjoint g ph
  disjoint v z
  disjoint ph v
  disjoint ph z
  disjoint U v
  disjoint U z
  disjoint F f
  disjoint F g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint X f
  disjoint X g
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y v
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint G f
  disjoint G g
  disjoint U x
  disjoint U y
  disjoint Z f
  disjoint Z g
  disjoint Z v
  disjoint Z z
  assert |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U |-> ( g e. ( z ^m ( 2nd ` v ) ) , f e. ( ( 2nd ` v ) ^m ( 1st ` v ) ) |-> ( g o. f ) ) ) )

  proof
    wph
    c.x
    vv
    vz
    cU
    cU
    cxp
    #
    cU
    vg
    vf
    vz
    cv
    vv
    cv
    #
    c2nd
    cfv
    #
    cmap
    co
    @2
    @1
    c1st
    cfv
    cmap
    co
    vg
    cv
    vf
    cv
    ccom
    cmpt2
    #
    cmpt2
    #
    cnx
    cbs
    cfv
    cU
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
    @4
    cop
    #
    ctp
    cC
    cco
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
    cC
    @4
    cU
    vf
    vg
    @6
    cV
    setcbas.c
    setcbas.u
    wph
    vx
    vy
    cC
    cU
    @6
    cV
    setcbas.c
    setcbas.u
    @6
    eqid
    setchomfval
    wph
    @4
    eqidd
    setcval
    @4
    cU
    @6
    catstr
    ccoid
    @5
    @7
    @8
    snsstp3
    wph
    @0
    cvv
    wcel
    #
    cU
    cV
    wcel
    #
    @4
    cvv
    wcel
    wph
    @10
    @10
    @9
    setcbas.u
    setcbas.u
    cU
    cU
    cV
    cV
    xpexg
    syl2anc
    setcbas.u
    vv
    vz
    @0
    cU
    @3
    cvv
    cV
    mpt2exga
    syl2anc
    setcco.o
    strfv3
end
