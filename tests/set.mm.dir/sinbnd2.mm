include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "resincl.mm"
include "sinbnd.mm"
include "simpld.mm"
include "simprd.mm"
include "neg1rr.mm"
include "1re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"

theorem sinbnd2
  let cA: class A


  assert |- ( A e. RR -> ( sin ` A ) e. ( -u 1 [,] 1 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    csin
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
    resincl
    @0
    @3
    @4
    cA
    sinbnd
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
