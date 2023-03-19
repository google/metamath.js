include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cif.mm"
include "ressval.mm"
include "iftrue.mm"
include "sylan9eqr.mm"
include "3impb.mm"

theorem ressid2
  let cA: class A
  let cB: class B
  let cR: class R
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vw: setvar w
  assume ressbas.r: |- R = ( W |`s A )
  assume ressbas.b: |- B = ( Base ` W )


  assert |- ( ( B C_ A /\ W e. X /\ A e. Y ) -> R = W )

  proof
    cB
    cA
    wss
    #
    cW
    cX
    wcel
    #
    cA
    cY
    wcel
    #
    cR
    cW
    wceq
    @1
    @2
    wa
    @0
    cR
    @0
    cW
    cW
    cnx
    cbs
    cfv
    cA
    cB
    cin
    cop
    csts
    co
    #
    cif
    cW
    cA
    cB
    cR
    cW
    cX
    cY
    ressbas.r
    ressbas.b
    ressval
    @0
    cW
    @3
    iftrue
    sylan9eqr
    3impb
end
