include "wcel.mm"
include "wa.mm"
include "psubssat.mm"
include "sseld.mm"
include "3impia.mm"

theorem psubatN
  let cA: class A
  let cB: class B
  let cS: class S
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume atpsub.a: |- A = ( Atoms ` K )
  assume atpsub.s: |- S = ( PSubSp ` K )


  assert |- ( ( K e. B /\ X e. S /\ Y e. X ) -> Y e. A )

  proof
    cK
    cB
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cX
    wcel
    cY
    cA
    wcel
    @0
    @1
    wa
    cX
    cA
    cY
    cA
    cB
    cS
    cK
    cX
    atpsub.a
    atpsub.s
    psubssat
    sseld
    3impia
end
