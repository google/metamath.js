include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cmpt2.mm"
include "cnx.mm"
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
include "estrcval.mm"
include "catstr.mm"
include "homid.mm"
include "snsstp2.mm"
include "wcel.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "strfv3.mm"

theorem estrchomfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vz: setvar z
  assume estrcbas.c: |- C = ( ExtStrCat ` U )
  assume estrcbas.u: |- ( ph -> U e. V )
  assume estrchomfval.h: |- H = ( Hom ` C )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint U x
  disjoint U y
  disjoint f g
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x z
  disjoint y z
  disjoint ph v
  disjoint ph z
  disjoint U v
  disjoint U z
  assert |- ( ph -> H = ( x e. U , y e. U |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) )

  proof
    wph
    cH
    vx
    vy
    cU
    cU
    vy
    cv
    cbs
    cfv
    vx
    cv
    cbs
    cfv
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
    cbs
    cfv
    vv
    cv
    #
    c2nd
    cfv
    cbs
    cfv
    #
    cmap
    co
    @5
    @4
    c1st
    cfv
    cbs
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
    estrcbas.c
    estrcbas.u
    wph
    @1
    eqidd
    wph
    @6
    eqidd
    estrcval
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
    estrcbas.u
    estrcbas.u
    vx
    vy
    cU
    cU
    @0
    cV
    cV
    mpt2exga
    syl2anc
    estrchomfval.h
    strfv3
end
