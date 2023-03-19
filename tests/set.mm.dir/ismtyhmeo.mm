include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cismty.mm"
include "co.mm"
include "chmeo.mm"
include "cv.mm"
include "ccn.mm"
include "ccnv.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "ismtyhmeolem.mm"
include "ismtycnv.mm"
include "imp.mm"
include "ishmeo.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ismtyhmeo
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let vf: setvar f
  let wph: wff ph
  assume ismtyhmeo.1: |- J = ( MetOpen ` M )
  assume ismtyhmeo.2: |- K = ( MetOpen ` N )


  assert |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) -> ( M Ismty N ) C_ ( J Homeo K ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    wa
    #
    vf
    cM
    cN
    cismty
    co
    #
    cJ
    cK
    chmeo
    co
    #
    @2
    vf
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @5
    cJ
    cK
    ccn
    co
    wcel
    @5
    ccnv
    #
    cK
    cJ
    ccn
    co
    wcel
    @7
    @8
    @5
    cJ
    cK
    cM
    cN
    cX
    cY
    ismtyhmeo.1
    ismtyhmeo.2
    @0
    @1
    @6
    simpll
    #
    @0
    @1
    @6
    simplr
    #
    @2
    @6
    simpr
    ismtyhmeolem
    @8
    @9
    cK
    cJ
    cN
    cM
    cY
    cX
    ismtyhmeo.2
    ismtyhmeo.1
    @11
    @10
    @2
    @6
    @9
    cN
    cM
    cismty
    co
    wcel
    @5
    cM
    cN
    cX
    cY
    ismtycnv
    imp
    ismtyhmeolem
    @5
    cJ
    cK
    ishmeo
    sylanbrc
    ex
    ssrdv
end
