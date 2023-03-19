include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "cwwlksn.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cwwlks.mm"
include "crab.mm"
include "wi.mm"
include "wa.mm"
include "cmpt2.mm"
include "df-wwlksn.mm"
include "a1i.mm"
include "fveq2.mm"
include "adantl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "adantr.mm"
include "rabeqbidv.mm"
include "simpl.mm"
include "simpr.mm"
include "fvex.mm"
include "rabex.mm"
include "ovmpt2d.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "reldmmpt2.mm"
include "ovprc2.mm"
include "fvprc.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem wwlksn
  let vw: setvar w
  let cG: class G
  let cN: class N
  let vg: setvar g
  let vn: setvar n

  disjoint G w
  disjoint N w
  disjoint G g
  disjoint G n
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint N g
  disjoint N n
  assert |- ( N e. NN0 -> ( N WWalksN G ) = { w e. ( WWalks ` G ) | ( # ` w ) = ( N + 1 ) } )

  proof
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cG
    cwwlksn
    co
    #
    vw
    cv
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    vw
    cG
    cwwlks
    cfv
    #
    crab
    #
    wceq
    #
    wi
    @1
    @0
    @8
    @1
    @0
    wa
    #
    vn
    vg
    cN
    cG
    cn0
    cvv
    @3
    vn
    cv
    #
    c1
    caddc
    co
    #
    wceq
    #
    vw
    vg
    cv
    #
    cwwlks
    cfv
    #
    crab
    #
    @7
    cwwlksn
    cvv
    cwwlksn
    vn
    vg
    cn0
    cvv
    @15
    cmpt2
    wceq
    @9
    vw
    vg
    vn
    df-wwlksn
    #
    a1i
    @10
    cN
    wceq
    #
    @13
    cG
    wceq
    #
    wa
    #
    @15
    @7
    wceq
    @9
    @19
    @12
    @5
    vw
    @14
    @6
    @18
    @14
    @6
    wceq
    @17
    @13
    cG
    cwwlks
    fveq2
    adantl
    @17
    @12
    @5
    wb
    @18
    @17
    @11
    @4
    @3
    @10
    cN
    c1
    caddc
    oveq1
    eqeq2d
    adantr
    rabeqbidv
    adantl
    @1
    @0
    simpl
    @1
    @0
    simpr
    @7
    cvv
    wcel
    @9
    @5
    vw
    @6
    cG
    cwwlks
    fvex
    rabex
    a1i
    ovmpt2d
    expcom
    @0
    wn
    #
    @8
    @1
    @20
    @2
    c0
    @7
    cN
    cG
    cwwlksn
    vn
    vg
    cn0
    cvv
    @15
    cwwlksn
    @16
    reldmmpt2
    ovprc2
    @20
    @7
    @5
    vw
    c0
    crab
    c0
    @20
    @5
    vw
    @6
    c0
    cG
    cwwlks
    fvprc
    rabeqdv
    @5
    vw
    rab0
    syl6eq
    eqtr4d
    a1d
    pm2.61i
end
