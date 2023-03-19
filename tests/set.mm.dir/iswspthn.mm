include "cv.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksn.mm"
include "co.mm"
include "cwwspthsn.mm"
include "wceq.mm"
include "breq2.mm"
include "exbidv.mm"
include "wspthsn.mm"
include "elrab2.mm"

theorem iswspthn
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cW: class W
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w

  disjoint G f
  disjoint W f
  disjoint G g
  disjoint G n
  disjoint G w
  disjoint f g
  disjoint f n
  disjoint f w
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint N g
  disjoint N n
  disjoint N w
  disjoint W w
  assert |- ( W e. ( N WSPathsN G ) <-> ( W e. ( N WWalksN G ) /\ E. f f ( SPaths ` G ) W ) )

  proof
    vf
    cv
    #
    vw
    cv
    #
    cG
    cspths
    cfv
    #
    wbr
    #
    vf
    wex
    @0
    cW
    @2
    wbr
    #
    vf
    wex
    vw
    cW
    cN
    cG
    cwwlksn
    co
    cN
    cG
    cwwspthsn
    co
    @1
    cW
    wceq
    @3
    @4
    vf
    @1
    cW
    @0
    @2
    breq2
    exbidv
    vw
    vf
    cG
    cN
    wspthsn
    elrab2
end
