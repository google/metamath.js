include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "chash.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "wb.mm"
include "eqeq2.mm"
include "adantr.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "fvex.mm"
include "ovmpt2a.mm"

theorem rusgrnumwwlklem
  let vw: setvar w
  let vv: setvar v
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cL: class L
  let cN: class N
  let cV: class V
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
  assert |- ( ( P e. V /\ N e. NN0 ) -> ( P L N ) = ( # ` { w e. ( N WWalksN G ) | ( w ` 0 ) = P } ) )

  proof
    vv
    vn
    cP
    cN
    cV
    cn0
    cc0
    vw
    cv
    cfv
    #
    vv
    cv
    #
    wceq
    #
    vw
    vn
    cv
    #
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    @0
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
    cL
    @1
    cP
    wceq
    #
    @3
    cN
    wceq
    #
    wa
    #
    @5
    @8
    chash
    @11
    @2
    @6
    vw
    @4
    @7
    @10
    @4
    @7
    wceq
    @9
    @3
    cN
    cG
    cwwlksn
    oveq1
    adantl
    @9
    @2
    @6
    wb
    @10
    @1
    cP
    @0
    eqeq2
    adantr
    rabeqbidv
    fveq2d
    rusgrnumwwlk.l
    @8
    chash
    fvex
    ovmpt2a
end
