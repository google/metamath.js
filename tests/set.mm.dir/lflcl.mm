include "wcel.mm"
include "w3a.mm"
include "wf.mm"
include "lflf.mm"
include "3adant3.mm"
include "simp3.mm"
include "ffvelrnd.mm"

theorem lflcl
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lflf.d: |- D = ( Scalar ` W )
  assume lflf.k: |- K = ( Base ` D )
  assume lflf.v: |- V = ( Base ` W )
  assume lflf.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. Y /\ G e. F /\ X e. V ) -> ( G ` X ) e. K )

  proof
    cW
    cY
    wcel
    #
    cG
    cF
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    cV
    cK
    cX
    cG
    @0
    @1
    cV
    cK
    cG
    wf
    @2
    cD
    cF
    cG
    cK
    cV
    cW
    cY
    lflf.d
    lflf.k
    lflf.v
    lflf.f
    lflf
    3adant3
    @0
    @1
    @2
    simp3
    ffvelrnd
end
