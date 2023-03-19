include "csrg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "co.mm"
include "eqid.mm"
include "srgmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndcl.mm"
include "syl3an1.mm"

theorem srgcl
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume srgcl.b: |- B = ( Base ` R )
  assume srgcl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. SRing /\ X e. B /\ Y e. B ) -> ( X .x. Y ) e. B )

  proof
    cR
    csrg
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
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
    cB
    wcel
    cR
    @0
    @0
    eqid
    #
    srgmgp
    cB
    c.x
    @0
    cX
    cY
    cB
    cR
    @0
    @1
    srgcl.b
    mgpbas
    cR
    c.x
    @0
    @1
    srgcl.t
    mgpplusg
    mndcl
    syl3an1
end
