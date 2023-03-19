include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cmap.mm"
include "co.mm"
include "cof.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndvcl.mm"
include "syl3an1.mm"

theorem ringvcl
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cX: class X
  let cY: class Y
  assume ringvcl.b: |- B = ( Base ` R )
  assume ringvcl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ X e. ( B ^m I ) /\ Y e. ( B ^m I ) ) -> ( X oF .x. Y ) e. ( B ^m I ) )

  proof
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    cX
    cB
    cI
    cmap
    co
    #
    wcel
    cY
    @1
    wcel
    cX
    cY
    c.x
    cof
    co
    @1
    wcel
    cR
    @0
    @0
    eqid
    #
    ringmgp
    cB
    c.x
    cI
    @0
    cX
    cY
    cB
    cR
    @0
    @2
    ringvcl.b
    mgpbas
    cR
    c.x
    @0
    @2
    ringvcl.t
    mgpplusg
    mndvcl
    syl3an1
end
