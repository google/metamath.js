include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cword.mm"
include "crab.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "cexp.mm"
include "wrdnval.mm"
include "fveq2d.mm"
include "fzofi.mm"
include "a1i.mm"
include "hashmap.mm"
include "sylan2.mm"
include "hashfzo0.mm"
include "adantl.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem hashwrdn
  let vw: setvar w
  let cN: class N
  let cV: class V

  disjoint N w
  disjoint V w
  assert |- ( ( V e. Fin /\ N e. NN0 ) -> ( # ` { w e. Word V | ( # ` w ) = N } ) = ( ( # ` V ) ^ N ) )

  proof
    cV
    cfn
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    vw
    cv
    chash
    cfv
    cN
    wceq
    vw
    cV
    cword
    crab
    #
    chash
    cfv
    cV
    cc0
    cN
    cfzo
    co
    #
    cmap
    co
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    #
    @4
    chash
    cfv
    #
    cexp
    co
    #
    @7
    cN
    cexp
    co
    @2
    @3
    @5
    chash
    vw
    cN
    cV
    cfn
    wrdnval
    fveq2d
    @1
    @0
    @4
    cfn
    wcel
    #
    @6
    @9
    wceq
    @10
    @1
    cc0
    cN
    fzofi
    a1i
    cV
    @4
    hashmap
    sylan2
    @2
    @8
    cN
    @7
    cexp
    @1
    @8
    cN
    wceq
    @0
    cN
    hashfzo0
    adantl
    oveq2d
    3eqtrd
end
