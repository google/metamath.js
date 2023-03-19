include "ccrg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "crngmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cmncom.mm"
include "syl3an1.mm"

theorem crngcom
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume ringcl.b: |- B = ( Base ` R )
  assume ringcl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. CRing /\ X e. B /\ Y e. B ) -> ( X .x. Y ) = ( Y .x. X ) )

  proof
    cR
    ccrg
    wcel
    cR
    cmgp
    cfv
    #
    ccmn
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.x
    co
    cY
    cX
    c.x
    co
    wceq
    cR
    @0
    @0
    eqid
    #
    crngmgp
    cB
    c.x
    @0
    cX
    cY
    cB
    cR
    @0
    @1
    ringcl.b
    mgpbas
    cR
    c.x
    @0
    @1
    ringcl.t
    mgpplusg
    cmncom
    syl3an1
end
