include "cxp.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmap.mm"
include "co.mm"
include "c1st.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cnx.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cvv.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqid.mm"
include "estrchomfval.mm"
include "eqidd.mm"
include "estrcval.mm"
include "catstr.mm"
include "ccoid.mm"
include "snsstp3.mm"
include "wcel.mm"
include "sqxpexg.mm"
include "syl.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "strfv3.mm"

theorem estrccofval
  let wph: wff ph
  let vz: setvar z
  let vv: setvar v
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume estrcbas.c: |- C = ( ExtStrCat ` U )
  assume estrcbas.u: |- ( ph -> U e. V )
  assume estrcco.o: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f v
  disjoint f z
  disjoint g v
  disjoint g z
  disjoint v z
  disjoint ph v
  disjoint ph z
  disjoint U v
  disjoint U z
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint ph y
  disjoint U x
  disjoint U y
  assert |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U |-> ( g e. ( ( Base ` z ) ^m ( Base ` ( 2nd ` v ) ) ) , f e. ( ( Base ` ( 2nd ` v ) ) ^m ( Base ` ( 1st ` v ) ) ) |-> ( g o. f ) ) ) )

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
    @2
    @1
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
    estrcbas.c
    estrcbas.u
    wph
    vx
    vy
    cC
    cU
    @6
    cV
    estrcbas.c
    estrcbas.u
    @6
    eqid
    estrchomfval
    wph
    @4
    eqidd
    estrcval
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
    @9
    estrcbas.u
    cU
    cV
    sqxpexg
    syl
    estrcbas.u
    vv
    vz
    @0
    cU
    @3
    cvv
    cV
    mpt2exga
    syl2anc
    estrcco.o
    strfv3
end
