include "crusgr.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "crab.mm"
include "chash.mm"
include "cn0.mm"
include "simpr.mm"
include "1nn0.mm"
include "rusgrnumwwlklem.mm"
include "sylancl.mm"
include "rusgrnumwwlkl1.mm"
include "eqtrd.mm"

theorem rusgrnumwwlkb1
  let vw: setvar w
  let vv: setvar v
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let cV: class V
  let cN: class N
  assume rusgrnumwwlk.v: |- V = ( Vtx ` G )
  assume rusgrnumwwlk.l: |- L = ( v e. V , n e. NN0 |-> ( # ` { w e. ( n WWalksN G ) | ( w ` 0 ) = v } ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint P n
  disjoint P v
  disjoint P w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint K w
  disjoint N n
  disjoint N v
  disjoint N w
  assert |- ( ( G RegUSGraph K /\ P e. V ) -> ( P L 1 ) = K )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cP
    cV
    wcel
    #
    wa
    #
    cP
    c1
    cL
    co
    #
    cc0
    vw
    cv
    cfv
    cP
    wceq
    vw
    c1
    cG
    cwwlksn
    co
    crab
    chash
    cfv
    #
    cK
    @2
    @1
    c1
    cn0
    wcel
    @3
    @4
    wceq
    @0
    @1
    simpr
    1nn0
    vw
    vv
    cP
    vn
    cG
    cL
    c1
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlklem
    sylancl
    vw
    cP
    cG
    cK
    cV
    rusgrnumwwlk.v
    rusgrnumwwlkl1
    eqtrd
end
