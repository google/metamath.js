include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "eqid.mm"
include "ellkr.mm"
include "simprbda.mm"
include "3impa.mm"

theorem lkrcl
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lkrcl.v: |- V = ( Base ` W )
  assume lkrcl.f: |- F = ( LFnl ` W )
  assume lkrcl.k: |- K = ( LKer ` W )


  assert |- ( ( W e. Y /\ G e. F /\ X e. ( K ` G ) ) -> X e. V )

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
    cG
    cK
    cfv
    wcel
    #
    cX
    cV
    wcel
    #
    @0
    @1
    wa
    @2
    @3
    cX
    cG
    cfv
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    @4
    cF
    cG
    cK
    cV
    cW
    cX
    cY
    @5
    lkrcl.v
    @4
    eqid
    @5
    eqid
    lkrcl.f
    lkrcl.k
    ellkr
    simprbda
    3impa
end
