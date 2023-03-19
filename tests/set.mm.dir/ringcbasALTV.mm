include "crg.mm"
include "cin.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "chom.mm"
include "cv.mm"
include "crh.mm"
include "co.mm"
include "cmpt2.mm"
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
include "ringcvalALTV.mm"
include "catstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "wcel.mm"
include "inex1g.mm"
include "syl.mm"
include "strfv3.mm"

theorem ringcbasALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume ringcbasALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcbasALTV.b: |- B = ( Base ` C )
  assume ringcbasALTV.u: |- ( ph -> U e. V )


  assert |- ( ph -> B = ( U i^i Ring ) )

  proof
    wph
    cB
    cU
    crg
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
    crh
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
    vf
    vg
    vv
    cv
    #
    c2nd
    cfv
    #
    vz
    cv
    crh
    co
    @4
    c1st
    cfv
    @5
    crh
    co
    vf
    cv
    vg
    cv
    ccom
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
    @6
    cU
    vg
    vf
    @2
    cV
    ringcbasALTV.c
    ringcbasALTV.u
    wph
    @0
    eqidd
    wph
    @2
    eqidd
    wph
    @6
    eqidd
    ringcvalALTV
    @6
    @0
    @2
    catstr
    baseid
    @1
    @3
    @7
    snsstp1
    wph
    cU
    cV
    wcel
    @0
    cvv
    wcel
    ringcbasALTV.u
    cU
    crg
    cV
    inex1g
    syl
    ringcbasALTV.b
    strfv3
end
