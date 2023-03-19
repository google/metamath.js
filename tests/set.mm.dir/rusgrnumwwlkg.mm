include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "chash.mm"
include "cmpt2.mm"
include "cexp.mm"
include "3simpc.mm"
include "adantl.mm"
include "eqid.mm"
include "rusgrnumwwlklem.mm"
include "syl.mm"
include "rusgrnumwwlk.mm"
include "eqtr3d.mm"

theorem rusgrnumwwlkg
  let vw: setvar w
  let cP: class P
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  assume rusgrnumwwlkg.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint K w
  disjoint N w
  disjoint P w
  disjoint V w
  disjoint G n
  disjoint G v
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint P n
  disjoint P v
  disjoint V n
  disjoint V v
  assert |- ( ( G RegUSGraph K /\ ( V e. Fin /\ P e. V /\ N e. NN0 ) ) -> ( # ` { w e. ( N WWalksN G ) | ( w ` 0 ) = P } ) = ( K ^ N ) )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cV
    cfn
    wcel
    #
    cP
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    wa
    #
    cP
    cN
    vv
    vn
    cV
    cn0
    cc0
    vw
    cv
    cfv
    #
    vv
    cv
    wceq
    vw
    vn
    cv
    cG
    cwwlksn
    co
    crab
    chash
    cfv
    cmpt2
    #
    co
    #
    @6
    cP
    wceq
    vw
    cN
    cG
    cwwlksn
    co
    crab
    chash
    cfv
    #
    cK
    cN
    cexp
    co
    @5
    @2
    @3
    wa
    #
    @8
    @9
    wceq
    @4
    @10
    @0
    @1
    @2
    @3
    3simpc
    adantl
    vw
    vv
    cP
    vn
    cG
    @7
    cN
    cV
    rusgrnumwwlkg.v
    @7
    eqid
    #
    rusgrnumwwlklem
    syl
    vw
    vv
    cP
    vn
    cG
    cK
    @7
    cN
    cV
    rusgrnumwwlkg.v
    @11
    rusgrnumwwlk
    eqtr3d
end
