include "wss.mm"
include "wn.mm"
include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cif.mm"
include "ressval.mm"
include "iffalse.mm"
include "sylan9eqr.mm"
include "3impb.mm"

theorem ressval2
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


  assert |- ( ( -. B C_ A /\ W e. X /\ A e. Y ) -> R = ( W sSet <. ( Base ` ndx ) , ( A i^i B ) >. ) )

  proof
    cB
    cA
    wss
    #
    wn
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
    wceq
    @2
    @3
    wa
    @1
    cR
    @0
    cW
    @4
    cif
    @4
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
    @4
    iffalse
    sylan9eqr
    3impb
end
