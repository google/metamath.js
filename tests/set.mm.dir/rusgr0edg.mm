include "cc0.mm"
include "crusgr.mm"
include "wbr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "crab.mm"
include "chash.mm"
include "cn0.mm"
include "simp2.mm"
include "nnnn0.mm"
include "3ad2ant3.mm"
include "rusgrnumwwlklem.mm"
include "syl2anc.mm"
include "c0.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cedg.mm"
include "cusgr.mm"
include "rusgrusgr.mm"
include "usgr0edg0rusgr.mm"
include "biimpcd.mm"
include "mpd.mm"
include "0enwwlksnge1.mm"
include "sylan.mm"
include "eleq2.mm"
include "noel.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "syl.mm"
include "3adant2.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem rusgr0edg
  let vw: setvar w
  let vv: setvar v
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cL: class L
  let cN: class N
  let cV: class V
  let cK: class K
  let vi: setvar i
  assume rusgrnumwwlk.v: |- V = ( Vtx ` G )
  assume rusgrnumwwlk.l: |- L = ( v e. V , n e. NN0 |-> ( # ` { w e. ( n WWalksN G ) | ( w ` 0 ) = v } ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint P n
  disjoint P v
  disjoint P w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint K w
  disjoint G i
  disjoint i w
  disjoint N i
  assert |- ( ( G RegUSGraph 0 /\ P e. V /\ N e. NN ) -> ( P L N ) = 0 )

  proof
    cG
    cc0
    crusgr
    wbr
    #
    cP
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cP
    cN
    cL
    co
    #
    cc0
    vw
    cv
    #
    cfv
    cP
    wceq
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    #
    cc0
    @3
    @1
    cN
    cn0
    wcel
    #
    @4
    @9
    wceq
    @0
    @1
    @2
    simp2
    @2
    @0
    @10
    @1
    cN
    nnnn0
    3ad2ant3
    vw
    vv
    cP
    vn
    cG
    cL
    cN
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlklem
    syl2anc
    @3
    @9
    c0
    chash
    cfv
    cc0
    @3
    @8
    c0
    chash
    @3
    @6
    wn
    #
    vw
    @7
    wral
    @8
    c0
    wceq
    @3
    @11
    vw
    @7
    @0
    @2
    @5
    @7
    wcel
    #
    @11
    wi
    #
    @1
    @0
    @2
    wa
    @7
    c0
    wceq
    #
    @13
    @0
    cG
    cedg
    cfv
    c0
    wceq
    #
    @2
    @14
    @0
    cG
    cusgr
    wcel
    #
    @15
    cG
    cc0
    rusgrusgr
    @16
    @0
    @15
    cG
    usgr0edg0rusgr
    biimpcd
    mpd
    cG
    cN
    0enwwlksnge1
    sylan
    @14
    @12
    @5
    c0
    wcel
    #
    @11
    @7
    c0
    @5
    eleq2
    @17
    @11
    @5
    noel
    pm2.21i
    syl6bi
    syl
    3adant2
    ralrimiv
    @6
    vw
    @7
    rabeq0
    sylibr
    fveq2d
    hash0
    syl6eq
    eqtrd
end
