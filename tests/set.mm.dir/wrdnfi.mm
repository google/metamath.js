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
include "cexp.mm"
include "co.mm"
include "hashwrdn.mm"
include "hashcl.mm"
include "nn0expcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "wrdexg.mm"
include "adantr.mm"
include "rabexg.mm"
include "hashclb.mm"
include "3syl.mm"
include "mpbird.mm"

theorem wrdnfi
  let vw: setvar w
  let cN: class N
  let cV: class V

  disjoint N w
  disjoint V w
  assert |- ( ( V e. Fin /\ N e. NN0 ) -> { w e. Word V | ( # ` w ) = N } e. Fin )

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
    #
    vw
    cV
    cword
    #
    crab
    #
    cfn
    wcel
    #
    @5
    chash
    cfv
    #
    cn0
    wcel
    #
    @2
    @7
    cV
    chash
    cfv
    #
    cN
    cexp
    co
    #
    cn0
    vw
    cN
    cV
    hashwrdn
    @0
    @9
    cn0
    wcel
    @1
    @10
    cn0
    wcel
    cV
    hashcl
    @9
    cN
    nn0expcl
    sylan
    eqeltrd
    @2
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    @6
    @8
    wb
    @0
    @11
    @1
    cV
    cfn
    wrdexg
    adantr
    @3
    vw
    @4
    cvv
    rabexg
    @5
    cvv
    hashclb
    3syl
    mpbird
end
