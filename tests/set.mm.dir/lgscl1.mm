include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "lgsle1.mm"
include "wb.mm"
include "lgscl.mm"
include "zabsle1.mm"
include "syl.mm"
include "mpbird.mm"

theorem lgscl1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( A /L N ) e. { -u 1 , 0 , 1 } )

  proof
    cA
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cA
    cN
    clgs
    co
    #
    c1
    cneg
    cc0
    c1
    ctp
    wcel
    #
    @1
    cabs
    cfv
    c1
    cle
    wbr
    #
    cA
    cN
    lgsle1
    @0
    @1
    cz
    wcel
    @2
    @3
    wb
    cA
    cN
    lgscl
    @1
    zabsle1
    syl
    mpbird
end
