include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "nnge1.mm"
include "cr.mm"
include "wb.mm"
include "1re.mm"
include "nnre.mm"
include "lenlt.mm"
include "sylancr.mm"
include "mpbid.mm"

theorem nnnlt1
  let cA: class A


  assert |- ( A e. NN -> -. A < 1 )

  proof
    cA
    cn
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    cA
    c1
    clt
    wbr
    wn
    #
    cA
    nnge1
    @0
    c1
    cr
    wcel
    cA
    cr
    wcel
    @1
    @2
    wb
    1re
    cA
    nnre
    c1
    cA
    lenlt
    sylancr
    mpbid
end
