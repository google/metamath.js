include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "chom.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cmpt2.mm"
include "cco.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccom.mm"
include "ctp.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "catstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "strfv.mm"
include "syl.mm"
include "eqidd.mm"
include "estrcval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem estrcbas
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume estrcbas.c: |- C = ( ExtStrCat ` U )
  assume estrcbas.u: |- ( ph -> U e. V )


  assert |- ( ph -> U = ( Base ` C ) )

  proof
    wph
    cU
    cnx
    cbs
    cfv
    cU
    cop
    #
    cnx
    chom
    cfv
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
    cmpt2
    #
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
    @4
    @3
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
    #
    cbs
    cfv
    #
    cC
    cbs
    cfv
    wph
    cU
    cV
    wcel
    cU
    @8
    wceq
    estrcbas.u
    cU
    @7
    cbs
    cV
    c1
    c1
    c5
    cdc
    cop
    @5
    cU
    @1
    catstr
    baseid
    @0
    @2
    @6
    snsstp1
    strfv
    syl
    wph
    cC
    @7
    cbs
    wph
    vx
    vy
    vz
    vv
    cC
    @5
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
    @5
    eqidd
    estrcval
    fveq2d
    eqtr4d
end
