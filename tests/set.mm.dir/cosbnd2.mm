include "cr.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "recoscl.mm"
include "cosbnd.mm"
include "simpld.mm"
include "simprd.mm"
include "neg1rr.mm"
include "1re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"

theorem cosbnd2
  let cA: class A


  assert |- ( A e. RR -> ( cos ` A ) e. ( -u 1 [,] 1 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    ccos
    cfv
    #
    cr
    wcel
    c1
    cneg
    #
    @1
    cle
    wbr
    #
    @1
    c1
    cle
    wbr
    #
    @1
    @2
    c1
    cicc
    co
    wcel
    cA
    recoscl
    @0
    @3
    @4
    cA
    cosbnd
    #
    simpld
    @0
    @3
    @4
    @5
    simprd
    @2
    c1
    @1
    neg1rr
    1re
    elicc2i
    syl3anbrc
end
