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
include "ringcbasALTV.mm"
include "eqidd.mm"
include "ringcvalALTV.mm"
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

theorem ringchomfvalALTV
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vz: setvar z
  let vk: setvar k
  assume ringcbasALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcbasALTV.b: |- B = ( Base ` C )
  assume ringcbasALTV.u: |- ( ph -> U e. V )
  assume ringchomfvalALTV.h: |- H = ( Hom ` C )

  disjoint x y
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
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
  disjoint U v
  disjoint U z
  disjoint ph v
  disjoint ph z
  disjoint B v
  disjoint B z
  disjoint k x
  assert |- ( ph -> H = ( x e. B , y e. B |-> ( x RingHom y ) ) )

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
    crh
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
    @9
    ringchomfvalALTV.h
    wph
    cC
    @8
    chom
    wph
    vx
    vy
    vz
    vv
    cB
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
    cB
    cC
    cU
    cV
    ringcbasALTV.c
    ringcbasALTV.b
    ringcbasALTV.u
    ringcbasALTV
    wph
    @2
    eqidd
    wph
    @6
    eqidd
    ringcvalALTV
    fveq2d
    syl5eq
    @2
    cvv
    wcel
    @2
    @9
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
    ringcbasALTV.b
    cC
    cbs
    fvex
    eqeltri
    #
    @10
    mpt2ex
    @2
    @8
    chom
    cvv
    c1
    c1
    c5
    cdc
    cop
    @6
    cB
    @2
    catstr
    homid
    @0
    @3
    @7
    snsstp2
    strfv
    mp1i
    eqtr4d
end
