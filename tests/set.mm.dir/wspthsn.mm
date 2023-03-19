include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cv.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksn.mm"
include "crab.mm"
include "wceq.mm"
include "oveq12.mm"
include "wb.mm"
include "fveq2.mm"
include "breqd.mm"
include "exbidv.mm"
include "adantl.mm"
include "rabeqbidv.mm"
include "df-wspthsn.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cwwlks.mm"
include "df-wwlksn.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem wspthsn
  let vw: setvar w
  let vf: setvar f
  let cG: class G
  let cN: class N
  let vg: setvar g
  let vn: setvar n

  disjoint G f
  disjoint G w
  disjoint f w
  disjoint N w
  disjoint G g
  disjoint G n
  disjoint f g
  disjoint f n
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint N g
  disjoint N n
  assert |- ( N WSPathsN G ) = { w e. ( N WWalksN G ) | E. f f ( SPaths ` G ) w }

  proof
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    #
    cN
    cG
    cwwspthsn
    co
    #
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
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    wceq
    vn
    vg
    cN
    cG
    cn0
    cvv
    @2
    @3
    vg
    cv
    #
    cspths
    cfv
    #
    wbr
    #
    vf
    wex
    #
    vw
    vn
    cv
    #
    @9
    cwwlksn
    co
    #
    crab
    #
    @8
    cwwspthsn
    @13
    cN
    wceq
    #
    @9
    cG
    wceq
    #
    wa
    @12
    @6
    vw
    @14
    @7
    @13
    cN
    @9
    cG
    cwwlksn
    oveq12
    @17
    @12
    @6
    wb
    @16
    @17
    @11
    @5
    vf
    @17
    @10
    @4
    @2
    @3
    @9
    cG
    cspths
    fveq2
    breqd
    exbidv
    adantl
    rabeqbidv
    vw
    vf
    vg
    vn
    df-wspthsn
    #
    @6
    vw
    @7
    cN
    cG
    cwwlksn
    ovex
    rabex
    ovmpt2a
    @0
    wn
    #
    @1
    c0
    @8
    vn
    vg
    @15
    cwwspthsn
    cN
    cG
    cn0
    cvv
    @18
    mpt2ndm0
    @19
    @8
    @6
    vw
    c0
    crab
    c0
    @19
    @6
    vw
    @7
    c0
    vn
    vg
    @3
    chash
    cfv
    @13
    c1
    caddc
    co
    wceq
    vw
    @9
    cwwlks
    cfv
    crab
    cwwlksn
    cN
    cG
    cn0
    cvv
    vw
    vg
    vn
    df-wwlksn
    mpt2ndm0
    rabeqdv
    @6
    vw
    rab0
    syl6eq
    eqtr4d
    pm2.61i
end
