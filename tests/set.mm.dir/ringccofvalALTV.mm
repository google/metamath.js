include "cco.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "crh.mm"
include "co.mm"
include "c1st.mm"
include "ccom.mm"
include "cmpt2.mm"
include "ctp.mm"
include "ringcbasALTV.mm"
include "eqid.mm"
include "ringchomfvalALTV.mm"
include "eqidd.mm"
include "ringcvalALTV.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "sqxpexg.mm"
include "ax-mp.mm"
include "mpt2ex.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "catstr.mm"
include "ccoid.mm"
include "snsstp3.mm"
include "strfv.mm"
include "3eqtr4g.mm"

theorem ringccofvalALTV
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
  let vk: setvar k
  assume ringcbasALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcbasALTV.b: |- B = ( Base ` C )
  assume ringcbasALTV.u: |- ( ph -> U e. V )
  assume ringccoALTV.o: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f v
  disjoint f z
  disjoint g v
  disjoint g z
  disjoint v z
  disjoint U v
  disjoint U z
  disjoint ph v
  disjoint ph z
  disjoint B v
  disjoint B z
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |-> ( g e. ( ( 2nd ` v ) RingHom z ) , f e. ( ( 1st ` v ) RingHom ( 2nd ` v ) ) |-> ( g o. f ) ) ) )

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
    vg
    cv
    vf
    cv
    ccom
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
    @7
    wph
    cC
    @9
    cco
    wph
    vx
    vy
    vz
    vv
    cB
    cC
    @7
    cU
    vf
    vg
    @1
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
    vx
    vy
    cB
    cC
    cU
    @1
    cV
    ringcbasALTV.c
    ringcbasALTV.b
    ringcbasALTV.u
    @1
    eqid
    ringchomfvalALTV
    wph
    @7
    eqidd
    ringcvalALTV
    fveq2d
    ringccoALTV.o
    @7
    cvv
    wcel
    @7
    @10
    wceq
    vv
    vz
    @3
    cB
    @6
    cB
    cvv
    wcel
    @3
    cvv
    wcel
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
    cB
    cvv
    sqxpexg
    ax-mp
    @11
    mpt2ex
    @7
    @9
    cco
    cvv
    c1
    c1
    c5
    cdc
    cop
    @7
    cB
    @1
    catstr
    ccoid
    @0
    @2
    @8
    snsstp3
    strfv
    ax-mp
    3eqtr4g
end
