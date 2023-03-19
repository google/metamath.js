include "wss.mm"
include "wn.mm"
include "wcel.mm"
include "cnx.mm"
include "csca.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "wceq.mm"
include "wa.mm"
include "cif.mm"
include "resvval.mm"
include "iffalse.mm"
include "sylan9eqr.mm"
include "3impb.mm"

theorem resvval2
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  assume resvsca.r: |- R = ( W |`v A )
  assume resvsca.f: |- F = ( Scalar ` W )
  assume resvsca.b: |- B = ( Base ` F )


  assert |- ( ( -. B C_ A /\ W e. X /\ A e. Y ) -> R = ( W sSet <. ( Scalar ` ndx ) , ( F |`s A ) >. ) )

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
    csca
    cfv
    cF
    cA
    cress
    co
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
    cF
    cW
    cX
    cY
    resvsca.r
    resvsca.f
    resvsca.b
    resvval
    @0
    cW
    @4
    iffalse
    sylan9eqr
    3impb
end
