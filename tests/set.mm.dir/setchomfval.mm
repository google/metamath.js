include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cmpt2.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccom.mm"
include "ctp.mm"
include "cvv.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqidd.mm"
include "setcval.mm"
include "catstr.mm"
include "homid.mm"
include "snsstp2.mm"
include "wcel.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "strfv3.mm"

theorem setchomfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vv: setvar v
  let vz: setvar z
  let cX: class X
  let cY: class Y
  let cG: class G
  let cZ: class Z
  assume setcbas.c: |- C = ( SetCat ` U )
  assume setcbas.u: |- ( ph -> U e. V )
  assume setchomfval.h: |- H = ( Hom ` C )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint U x
  disjoint U y
  disjoint f g
  disjoint F f
  disjoint F g
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
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint x z
  disjoint y z
  disjoint ph z
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
  disjoint U v
  disjoint U z
  disjoint Z f
  disjoint Z g
  disjoint Z v
  disjoint Z z
  assert |- ( ph -> H = ( x e. U , y e. U |-> ( y ^m x ) ) )

  proof
    wph
    cH
    vx
    vy
    cU
    cU
    vy
    cv
    vx
    cv
    cmap
    co
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
    @1
    cop
    #
    cnx
    cco
    cfv
    vv
    vz
    cU
    cU
    cxp
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
    @5
    @4
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
    cmpt2
    #
    cop
    #
    ctp
    cC
    chom
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
    @6
    cU
    vf
    vg
    @1
    cV
    setcbas.c
    setcbas.u
    wph
    @1
    eqidd
    wph
    @6
    eqidd
    setcval
    @6
    cU
    @1
    catstr
    homid
    @2
    @3
    @7
    snsstp2
    wph
    cU
    cV
    wcel
    #
    @8
    @1
    cvv
    wcel
    setcbas.u
    setcbas.u
    vx
    vy
    cU
    cU
    @0
    cV
    cV
    mpt2exga
    syl2anc
    setchomfval.h
    strfv3
end
