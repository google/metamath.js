include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cwwlksn.mm"
include "cv.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "w3a.mm"
include "crab.mm"
include "df-wspthsn.mm"
include "elmpt2cl.mm"
include "simpl.mm"
include "wb.mm"
include "iswspthn.mm"
include "a1i.mm"
include "biimpa.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "mpancom.mm"

theorem wspthnp
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
  assert |- ( W e. ( N WSPathsN G ) -> ( ( N e. NN0 /\ G e. _V ) /\ W e. ( N WWalksN G ) /\ E. f f ( SPaths ` G ) W ) )

  proof
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    #
    cW
    cN
    cG
    cwwspthsn
    co
    wcel
    #
    @0
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    vf
    cv
    #
    cW
    cG
    cspths
    cfv
    wbr
    vf
    wex
    #
    w3a
    #
    vn
    vg
    cn0
    cvv
    @3
    vw
    cv
    vg
    cv
    #
    cspths
    cfv
    wbr
    vf
    wex
    vw
    vn
    cv
    @6
    cwwlksn
    co
    crab
    cN
    cG
    cwwspthsn
    cW
    vw
    vf
    vg
    vn
    df-wspthsn
    elmpt2cl
    @0
    @1
    wa
    @0
    @2
    @4
    wa
    #
    @5
    @0
    @1
    simpl
    @0
    @1
    @7
    @1
    @7
    wb
    @0
    vf
    cG
    cN
    cW
    iswspthn
    a1i
    biimpa
    @0
    @2
    @4
    3anass
    sylanbrc
    mpancom
end
