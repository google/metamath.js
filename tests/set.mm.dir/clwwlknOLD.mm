include "cvv.mm"
include "wcel.mm"
include "cn.mm"
include "cclwwlknold.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlk.mm"
include "crab.mm"
include "wi.mm"
include "wa.mm"
include "cmpt2.mm"
include "df-clwwlknOLD.mm"
include "a1i.mm"
include "fveq2.mm"
include "adantl.mm"
include "wb.mm"
include "eqeq2.mm"
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

theorem clwwlknOLD
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
  assert |- ( N e. NN -> ( N ClWWalksNOLD G ) = { w e. ( ClWWalks ` G ) | ( # ` w ) = N } )

  proof
    cG
    cvv
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cG
    cclwwlknold
    co
    #
    vw
    cv
    chash
    cfv
    #
    cN
    wceq
    #
    vw
    cG
    cclwwlk
    cfv
    #
    crab
    #
    wceq
    #
    wi
    @1
    @0
    @7
    @1
    @0
    wa
    #
    vn
    vg
    cN
    cG
    cn
    cvv
    @3
    vn
    cv
    #
    wceq
    #
    vw
    vg
    cv
    #
    cclwwlk
    cfv
    #
    crab
    #
    @6
    cclwwlknold
    cvv
    cclwwlknold
    vn
    vg
    cn
    cvv
    @13
    cmpt2
    wceq
    @8
    vw
    vg
    vn
    df-clwwlknOLD
    #
    a1i
    @9
    cN
    wceq
    #
    @11
    cG
    wceq
    #
    wa
    #
    @13
    @6
    wceq
    @8
    @17
    @10
    @4
    vw
    @12
    @5
    @16
    @12
    @5
    wceq
    @15
    @11
    cG
    cclwwlk
    fveq2
    adantl
    @15
    @10
    @4
    wb
    @16
    @9
    cN
    @3
    eqeq2
    adantr
    rabeqbidv
    adantl
    @1
    @0
    simpl
    @1
    @0
    simpr
    @6
    cvv
    wcel
    @8
    @4
    vw
    @5
    cG
    cclwwlk
    fvex
    rabex
    a1i
    ovmpt2d
    expcom
    @0
    wn
    #
    @7
    @1
    @18
    @2
    c0
    @6
    cN
    cG
    cclwwlknold
    vn
    vg
    cn
    cvv
    @13
    cclwwlknold
    @14
    reldmmpt2
    ovprc2
    @18
    @6
    @4
    vw
    c0
    crab
    c0
    @18
    @4
    vw
    @5
    c0
    cG
    cclwwlk
    fvprc
    rabeqdv
    @4
    vw
    rab0
    syl6eq
    eqtr4d
    a1d
    pm2.61i
end
