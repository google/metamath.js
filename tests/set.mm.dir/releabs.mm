include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cabs.mm"
include "recl.mm"
include "cr.mm"
include "recnd.mm"
include "abscl.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "leabs.mm"
include "absrele.mm"
include "letrd.mm"

theorem releabs
  let cA: class A


  assert |- ( A e. CC -> ( Re ` A ) <_ ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    @1
    cabs
    cfv
    #
    cA
    cabs
    cfv
    cA
    recl
    #
    @0
    @1
    cc
    wcel
    @2
    cr
    wcel
    @0
    @1
    @3
    recnd
    @1
    abscl
    syl
    cA
    abscl
    @0
    @1
    cr
    wcel
    @1
    @2
    cle
    wbr
    @3
    @1
    leabs
    syl
    cA
    absrele
    letrd
end
